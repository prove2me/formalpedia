-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch213
-- name    : Polychromatic418967fa_Branch213
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:22:45.684849+00:00
-- url     : https://prove2.me/theorems/ed9bedb6-08c2-4118-a547-491e74cfa8e4
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch213_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_213 : allB 213 213 :=
  allB_succ' 2 212 213 (Eq.refl Bool.true) (allA_succ_of_accept 1 212 213 (accept_3_4 1 212 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 212 213)) (allB_succ' 3 211 213 (Eq.refl Bool.true) (allA_succ_of_accept 2 211 213
  (accept_3_5 2 211 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 211 213
  (Polychromatic418967fa.accept_9_1_4_6_1_5 1 211 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 211 213))) (allB_succ' 4 210 213 (Eq.refl Bool.true) (allA_succ_of_gcd 3 210 213 3 1 70 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 210 213
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 210 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 210 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 210 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 210 213)))) (allB_succ' 5 209 213 (Eq.refl Bool.true) (allA_succ_of_accept 4
  209 213 (accept_3_4 4 209 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 209 213
  (Polychromatic418967fa.accept_9_3_2_6_1_264 3 209 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 209 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 209 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 209 213 (accept_3_4 1 209 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 209 213))))) (allB_succ' 6 208 213 (Eq.refl Bool.true) (allA_succ_of_accept 5 208 213
  (accept_3_5 5 208 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 208 213
  (Polychromatic418967fa.accept_9_4_1_6_1_284 4 208 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 208 213 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 208 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 208 213 (accept_3_5 2 208 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 208 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 208 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 208 213)))))) (allB_succ' 7 207 213 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 207 213 3 2 69 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 207 213 (Polychromatic418967fa.accept_10_5_7_3_1_561 5 207 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 207 213 (Polychromatic418967fa.accept_10_4_7_3_1_54 4 207 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 207 213 3 1 69 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 207 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 207 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 207 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 207 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 207 213))))))) (allB_succ' 8 206 213 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 206 213 (accept_3_4 7 206 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  206 213 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 206 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 206 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 206 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 206 213 (accept_3_4 4 206 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 206 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 206 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 206 213
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 206 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 206 213 (accept_3_4 1 206 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 206
  213)))))))) (allB_succ' 9 205 213 (Eq.refl Bool.true) (allA_succ_of_accept 8 205 213 (accept_3_5 8 205 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 205 213 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 205 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 205 213
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 205 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 205 213 (accept_3_5 5 205 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  205 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 205 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 205 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 205 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 205 213 (accept_3_5 2 205 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 205 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 205 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 205 213))))))))) (allB_succ' 10 204 213 (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 204 213 3 3 68 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 204 213 (Polychromatic418967fa.accept_15_8_9_3_1_1194 8 204 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 204 213 (Polychromatic418967fa.accept_10_7_4_3_1_560 7
  204 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 204 213 3 2 68 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 204 213
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 204 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 204 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 204 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 204 213 3 1 68 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 204 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 204 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 204 213
  (Polychromatic418967fa.accept_8_1_4_5_1_48 1 204 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 204 213)))))))))) (allB_succ' 11 203 213 (Eq.refl Bool.true) (allA_succ_of_accept 10 203 213 (accept_3_4 10
  203 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 203 213
  (Polychromatic418967fa.accept_15_9_8_3_1_557 9 203 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 203 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 203 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 203 213 (accept_3_4 7 203 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 203 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 203 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 203 213 (Polychromatic418967fa.accept_15_5_8_3_1_556 5
  203 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 203 213 (accept_3_4 4 203
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 203 213
  (Polychromatic418967fa.accept_9_3_5_6_1_253 3 203 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 203 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 203 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 203 213 (accept_3_4 1 203 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 203 213))))))))))) (allB_succ' 12 202 213 (Eq.refl Bool.true) (allA_succ_of_accept 11 202 213
  (accept_3_5 11 202 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 202 213
  (Polychromatic418967fa.accept_9_1_4_6_1_5 10 202 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 202 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 202 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 202 213 (accept_3_5 8 202 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 202 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 202 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 202 213 (Polychromatic418967fa.accept_12_6_10_9_1_531
  6 202 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 202 213 (accept_3_5 5
  202 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 202 213
  (Polychromatic418967fa.accept_7_4_6_3_1_271 4 202 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 202 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 202 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 202 213 (accept_3_5 2 202 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 202 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 202 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 202 213)))))))))))) (allB_succ' 13 201 213 (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 201 213 3 4 67 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 201 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 201 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 201 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 201 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 201 213 3 3 67 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 201 213
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 201 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 201 213 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 201 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 201 213 3 2 67 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 201 213 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 201 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 201 213
  (Polychromatic418967fa.accept_8_4_1_5_1_186 4 201 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 201 213 3 1 67 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 201 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 201 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 201 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 201 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 201 213))))))))))))) (allB_succ' 14 200 213
  (Eq.refl Bool.true) (allA_succ_of_accept 13 200 213 (accept_3_4 13 200 213 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 200 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 200 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 200 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 200 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 200 213 (accept_3_4 10 200 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 200 213 (Polychromatic418967fa.accept_11_9_2_4_1_707 9
  200 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 200 213
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 200 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 200 213 (accept_3_4 7 200 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  200 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 200 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 200 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 200 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 200 213 (accept_3_4 4 200 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 200 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 200 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 200 213
  (Polychromatic418967fa.accept_15_2_5_3_1_552 2 200 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 200 213 (accept_3_4 1 200 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 200
  213)))))))))))))) (allB_succ' 15 199 213 (Eq.refl Bool.true) (allA_succ_of_accept 14 199 213 (accept_3_5 14 199 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 199 213 (Polychromatic418967fa.accept_9_4_1_6_1_284
  13 199 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 199 213
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 199 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 199 213 (accept_3_5 11 199 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 199 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 199 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 199 213 (Polychromatic418967fa.accept_13_9_4_5_1_1651 9 199 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 199 213 (accept_3_5 8 199 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 199 213 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 199 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 199 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 199 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 199 213 (accept_3_5 5 199 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  199 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 199 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 199 213 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 199 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 199 213 (accept_3_5 2 199 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 199 213 (Polychromatic418967fa.accept_13_1_4_5_1_113 1 199 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 199 213))))))))))))))) (allB_succ' 16 198 213 (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 198 213 3 5 66 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 198 213 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 198 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 198 213 (Polychromatic418967fa.accept_7_6_2_3_1_107
  13 198 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 198 213 3 4 66 71
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 198 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 198 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 198 213 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 198 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 198 213 3 3 66 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 198 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 198 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 198 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 198 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 198 213 3 2 66 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 198 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 198 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 198 213 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 198 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 198 213 3 1 66 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 198 213
  (Polychromatic418967fa.accept_12_2_6_9_1_19 2 198 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 198 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 198 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 198 213)))))))))))))))) (allB_succ' 17 197 213 (Eq.refl Bool.true)
  (allA_succ_of_accept 16 197 213 (accept_3_4 16 197 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 197 213 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 197 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 197 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 197 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 197 213 (accept_3_4 13 197 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 197 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 197 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 197 213
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 197 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 197 213 (accept_3_4 10 197 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  197 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 197 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 197 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 197 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 197 213 (accept_3_4 7 197 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 197 213 (Polychromatic418967fa.accept_10_6_7_3_1_547 6 197 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 197 213
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 197 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 197 213 (accept_3_4 4 197 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  197 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 197 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 197 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 197 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 197 213 (accept_3_4 1 197 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 197 213))))))))))))))))) (allB_succ' 18 196 213 (Eq.refl Bool.true)
  (allA_succ_of_accept 17 196 213 (accept_3_5 17 196 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 196 213 (Polychromatic418967fa.accept_13_3_1_5_1_499 16 196 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 196 213 (Polychromatic418967fa.accept_16_15_4_5_1_1411 15 196 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 196 213 (accept_3_5 14 196 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 196 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 196 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 196 213
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 196 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 196 213 (accept_3_5 11 196 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 196 213 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 196 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 196 213 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 196 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 196 213 (accept_3_5 8 196 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 196 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 196 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 196 213
  (Polychromatic418967fa.accept_12_6_4_9_1_544 6 196 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 196 213 (accept_3_5 5 196 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  196 213 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 196 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 196 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 196 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 196 213 (accept_3_5 2 196 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 196 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 196 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 196 213)))))))))))))))))) (allB_succ' 19 195 213
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 195 213 3 6 65 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 195 213 (Polychromatic418967fa.accept_10_7_5_3_1_542 17 195 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 195 213
  (Polychromatic418967fa.accept_7_2_6_3_1_100 16 195 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 195 213 3 5 65 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 195 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 195 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 195 213 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 195
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 195 213 3 4 65 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 195 213
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 195 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 195 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 195 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 195 213 3 3 65 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 195 213 (Polychromatic418967fa.accept_10_8_5_3_1_543 8 195 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 195 213
  (Polychromatic418967fa.accept_10_7_5_3_1_542 7 195 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 195 213 3 2 65 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 195 213 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 195 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 195 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 195 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 195 213 3 1 65 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 195 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 195 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 195 213 (Polychromatic418967fa.accept_11_1_8_4_1_717 1 195 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 195 213))))))))))))))))))) (allB_succ' 20 194 213 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 194 213 (accept_3_4 19 194 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 194 213 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 194 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 194 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 194 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 194 213 (accept_3_4 16 194 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 194 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 194 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 194 213
  (Polychromatic418967fa.accept_11_3_7_4_1_1133 14 194 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 194 213 (accept_3_4 13 194 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 194 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 194 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 194 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 194 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 194 213 (accept_3_4 10 194 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 194 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 194 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 194 213
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 194 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 194 213 (accept_3_4 7 194 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  194 213 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 194 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 194 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 194 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 194 213 (accept_3_4 4 194 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 194 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 194 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 194 213
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 194 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 194 213 (accept_3_4 1 194 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 194
  213)))))))))))))))))))) (allB_succ' 21 193 213 (Eq.refl Bool.true) (allA_succ_of_accept 20 193 213 (accept_3_5 20 193
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 193 213 (Polychromatic418967fa.accept_9_1_4_6_1_5
  19 193 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 193 213
  (Polychromatic418967fa.accept_19_18_3_4_1_7079 18 193 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 193 213 (accept_3_5 17 193 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 193 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 193 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 193 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 193 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 193 213 (accept_3_5 14 193 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 193 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 193 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 193 213
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 193 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 193 213 (accept_3_5 11 193 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 193 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 193 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 193 213 (Polychromatic418967fa.accept_15_9_13_3_1_535 9 193 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 193 213 (accept_3_5 8 193 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 193 213 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 193 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 193 213
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 193 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 193 213 (accept_3_5 5 193 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  193 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 193 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 193 213 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 193 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 193 213 (accept_3_5 2 193 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 193 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 193 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 193 213))))))))))))))))))))) (allB_succ' 22 192 213
  (Eq.refl Bool.true) (allA_succ_of_gcd 21 192 213 3 7 64 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 192 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 192 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 192 213
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 192 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 192 213 3 6 64 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 192 213 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 192 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 192 213 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 192 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 192 213 3 5 64 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 192 213
  (Polychromatic418967fa.accept_9_5_3_6_1_269 14 192 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 192 213 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 192 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 192 213 3 4 64 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 192 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 11
  192 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 192 213
  (Polychromatic418967fa.accept_9_1_3_6_1_70 10 192 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 192 213 3 3 64 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 192 213 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 192 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 192 213 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 192 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 192 213 3 2 64 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 192 213
  (Polychromatic418967fa.accept_9_5_3_6_1_269 5 192 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 192 213 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 192 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 192 213 3 1 64 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 192 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 192 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 192 213
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 192 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 192 213)))))))))))))))))))))) (allB_succ' 23 191 213 (Eq.refl Bool.true) (allA_succ_of_accept 22 191 213
  (accept_3_4 22 191 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 191 213
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 191 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 191 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 191 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 191 213 (accept_3_4 19 191 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 191 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 191 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 191 213 (Polychromatic418967fa.accept_9_8_2_6_1_875
  17 191 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 191 213 (accept_3_4 16
  191 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 191 213
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 191 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 191 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 191 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 191 213 (accept_3_4 13 191 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 191 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 191 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 191 213
  (Polychromatic418967fa.accept_25_11_16_13_1_2000 11 191 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 191 213 (accept_3_4 10 191 213 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 191 213 (Polychromatic418967fa.accept_18_9_11_15_1_4616 9 191 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 191 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 191 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 191 213 (accept_3_4 7 191 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 191 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 6
  191 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 191 213
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 191 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 191 213 (accept_3_4 4 191 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  191 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 191 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 191 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 191 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 191 213 (accept_3_4 1 191 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 191 213))))))))))))))))))))))) (allB_succ' 24 190 213 (Eq.refl Bool.true)
  (allA_succ_of_accept 23 190 213 (accept_3_5 23 190 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 190 213 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 190 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 190 213 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 190 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 190 213 (accept_3_5 20 190 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 190 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 190 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 190 213
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 190 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 190 213 (accept_3_5 17 190 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 190 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 190 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 190 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 190 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 190 213 (accept_3_5 14 190 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 190 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 190 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 190 213
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 190 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 190 213 (accept_3_5 11 190 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 190 213 (Polychromatic418967fa.accept_13_10_8_5_1_1616 10 190 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 190 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 190 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 190 213 (accept_3_5 8 190 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 190 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 190 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 190 213
  (Polychromatic418967fa.accept_12_6_10_9_1_531 6 190 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 190 213 (accept_3_5 5 190 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  190 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 190 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 190 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 190 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 190 213 (accept_3_5 2 190 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 190 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 190 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 190 213)))))))))))))))))))))))) (allB_succ' 25 189 213
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 189 213 3 8 63 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 189 213 (Polychromatic418967fa.accept_15_8_9_3_1_1194 23 189 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 189 213
  (Polychromatic418967fa.accept_18_4_9_15_1_3383 22 189 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 189 213 3 7 63 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 189 213 (Polychromatic418967fa.accept_11_9_2_4_1_707 20 189 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 189 213 (Polychromatic418967fa.accept_20_19_9_13_1_2598 19 189
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 189 213 3 6 63 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 189 213
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 17 189 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 189 213 (Polychromatic418967fa.accept_10_6_9_3_1_935 16 189 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 189 213 3 5 63 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 189 213 (Polychromatic418967fa.accept_10_4_9_3_1_1907
  14 189 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 189 213
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 13 189 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 189 213 3 4 63 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 189 213 (Polychromatic418967fa.accept_13_11_7_5_1_2314 11 189 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 189 213 (Polychromatic418967fa.accept_14_10_7_3_1_1022 10 189
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 189 213 3 3 63 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 189 213
  (Polychromatic418967fa.accept_15_8_9_3_1_1194 8 189 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 189 213 (Polychromatic418967fa.accept_17_7_2_9_1_6396 7 189 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 189 213 3 2 63 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 189 213 (Polychromatic418967fa.accept_15_5_9_3_1_528 5 189 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 189 213
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 4 189 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 189 213 3 1 63 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 189 213 (Polychromatic418967fa.accept_13_2_7_5_1_3189 2 189 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 213 (Polychromatic418967fa.accept_16_1_13_5_1_2280 1 189
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 189 213)))))))))))))))))))))))))
  (allB_succ' 26 188 213 (Eq.refl Bool.true) (allA_succ_of_accept 25 188 213 (accept_3_4 25 188 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 188 213 (Polychromatic418967fa.accept_13_11_6_5_1_2339 24 188 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 188 213
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 188 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 188 213 (accept_3_4 22 188 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 188 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 188 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 188 213 (Polychromatic418967fa.accept_9_2_8_6_1_79 20 188 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 188 213 (accept_3_4 19 188 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 188 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 188 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 188 213
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 188 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 188 213 (accept_3_4 16 188 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 188 213 (Polychromatic418967fa.accept_10_5_8_3_1_229 15 188 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 188 213 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 188 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 188 213 (accept_3_4 13 188 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 188 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 188 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 188 213
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 188 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 188 213 (accept_3_4 10 188 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  188 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 188 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 188 213 (Polychromatic418967fa.accept_11_8_1_4_1_2318 8 188 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 188 213 (accept_3_4 7 188 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 188 213 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 188 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 188 213
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 188 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 188 213 (accept_3_4 4 188 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  188 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 188 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 188 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 188 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 188 213 (accept_3_4 1 188 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 188 213)))))))))))))))))))))))))) (allB_succ' 27 187 213 (Eq.refl Bool.true)
  (allA_succ_of_accept 26 187 213 (accept_3_5 26 187 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 187 213 (Polychromatic418967fa.accept_10_5_7_3_1_561 25 187 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 187 213 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 187 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 187 213 (accept_3_5 23 187 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 187 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 187 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 187 213
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 187 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 187 213 (accept_3_5 20 187 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 187 213 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 187 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 187 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 187 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 187 213 (accept_3_5 17 187 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 187 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 187 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 187 213
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 187 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 187 213 (accept_3_5 14 187 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 187 213 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 187 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 187 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 187 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 187 213 (accept_3_5 11 187 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 187 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 187 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 187 213
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 187 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 187 213 (accept_3_5 8 187 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  187 213 (Polychromatic418967fa.accept_16_7_11_5_1_4402 7 187 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 187 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 187 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 187 213 (accept_3_5 5 187 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 187 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 187 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 187 213
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 187 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 187 213 (accept_3_5 2 187 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  187 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 187 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 187 213))))))))))))))))))))))))))) (allB_succ' 28 186 213 (Eq.refl Bool.true) (allA_succ_of_gcd
  27 186 213 3 9 62 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 186 213 (Polychromatic418967fa.accept_12_2_6_9_1_19 26 186 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 186 213 (Polychromatic418967fa.accept_13_12_4_5_1_1637 25 186
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 186 213 3 8 62 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 186 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 186 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 186 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 186 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 186 213 3 7 62 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 186 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 20
  186 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 186 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 186 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 186 213 3 6 62 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 186 213 (Polychromatic418967fa.accept_10_7_6_3_1_927 17 186 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 186 213 (Polychromatic418967fa.accept_11_5_10_4_1_1157 16 186
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 186 213 3 5 62 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 186 213
  (Polychromatic418967fa.accept_12_2_6_9_1_19 14 186 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 186 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 186 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 186 213 3 4 62 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 186 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  186 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 186 213
  (Polychromatic418967fa.accept_12_10_6_9_1_549 10 186 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 186 213 3 3 62 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 186 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 186 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 186 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 186 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 186 213 3 2 62 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 186 213
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 5 186 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 186 213 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 186 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 186 213 3 1 62 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 186 213 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 186 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 186 213
  (Polychromatic418967fa.accept_7_1_4_3_1_21 1 186 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 186 213)))))))))))))))))))))))))))) (allB_succ' 29 185 213 (Eq.refl Bool.true) (allA_succ_of_accept 28 185
  213 (accept_3_4 28 185 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 185 213
  (Polychromatic418967fa.accept_10_7_5_3_1_542 27 185 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 185 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 185 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 185 213 (accept_3_4 25 185 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 185 213 (Polychromatic418967fa.accept_11_2_9_4_1_310 24 185 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 185 213
  (Polychromatic418967fa.accept_15_8_5_3_1_1990 23 185 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 185 213 (accept_3_4 22 185 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 185 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 185 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 185 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 185 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 185 213 (accept_3_4 19 185 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 185 213 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 185 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 185 213
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 185 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 185 213 (accept_3_4 16 185 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 185 213 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 185 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 185 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 185 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 185 213 (accept_3_4 13 185 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 185 213 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 185 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 185 213
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 185 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 185 213 (accept_3_4 10 185 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  185 213 (Polychromatic418967fa.accept_13_9_3_5_1_1605 9 185 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 185 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 185 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 185 213 (accept_3_4 7 185 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 185 213 (Polychromatic418967fa.accept_13_6_3_5_1_3167 6 185 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 185 213
  (Polychromatic418967fa.accept_22_5_9_15_1_7841 5 185 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 185 213 (accept_3_4 4 185 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  185 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 185 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 185 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 185 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 185 213 (accept_3_4 1 185 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 185 213))))))))))))))))))))))))))))) (allB_succ' 30 184 213 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 184 213 (accept_3_5 29 184 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 184 213 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 184 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 184 213 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 184 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 184 213 (accept_3_5 26 184 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 184 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 184 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 184 213
  (Polychromatic418967fa.accept_18_6_4_15_1_2276 24 184 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 184 213 (accept_3_5 23 184 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 184 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 184 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 184 213 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 184 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 184 213 (accept_3_5 20 184 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 184 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 184 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 184 213
  (Polychromatic418967fa.accept_11_7_8_4_1_718 18 184 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 184 213 (accept_3_5 17 184 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 184 213 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 184 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 184 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 184 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 184 213 (accept_3_5 14 184 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 184 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 184 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 184 213
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 184 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 184 213 (accept_3_5 11 184 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 184 213 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 184 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 184 213 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 184 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 184 213 (accept_3_5 8 184 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 184 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 184 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 184 213
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 184 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 184 213 (accept_3_5 5 184 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  184 213 (Polychromatic418967fa.accept_13_4_2_5_1_4045 4 184 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 184 213 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 184 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 184 213 (accept_3_5 2 184 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 184 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 184 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 184 213)))))))))))))))))))))))))))))) (allB_succ' 31 183
  213 (Eq.refl Bool.true) (allA_succ_of_gcd 30 183 213 3 10 61 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 183 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 183 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 183 213
  (Polychromatic418967fa.accept_9_1_3_6_1_70 28 183 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 183 213 3 9 61 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 183 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 183 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 183 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 183 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 183 213 3 8 61 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 183 213
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 183 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 183 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 183 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 183 213 3 7 61 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 183 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 20
  183 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 183 213
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 183 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 183 213 3 6 61 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 183 213 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 183 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 183 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 183 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 183 213 3 5 61 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 183 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 183 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 183 213 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 183 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 183 213 3 4 61 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 183 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 11
  183 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 183 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 183 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 183 213 3 3 61 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 183 213 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 183 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 213 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 183 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 183 213 3 2 61 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 183 213
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 183 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 183 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 183 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 183 213 3 1 61 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 183 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 183 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 213
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 183 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 183 213))))))))))))))))))))))))))))))) (allB_succ' 32 182 213 (Eq.refl Bool.true) (allA_succ_of_accept 31
  182 213 (accept_3_4 31 182 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 182 213
  (Polychromatic418967fa.accept_9_3_2_6_1_264 30 182 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 182 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 182 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 182 213 (accept_3_4 28 182 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 182 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 182 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 182 213 (Polychromatic418967fa.accept_9_8_2_6_1_875
  26 182 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 182 213 (accept_3_4 25
  182 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 182 213
  (Polychromatic418967fa.accept_11_2_6_4_1_3028 24 182 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 182 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 182 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 182 213 (accept_3_4 22 182 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 182 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 182 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 182 213 (Polychromatic418967fa.accept_15_5_2_3_1_4876
  20 182 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 182 213 (accept_3_4 19
  182 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 182 213
  (Polychromatic418967fa.accept_12_6_2_9_1_537 18 182 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 182 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 182 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 182 213 (accept_3_4 16 182 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 182 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 182 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 182 213 (Polychromatic418967fa.accept_9_5_2_6_1_265
  14 182 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 182 213 (accept_3_4 13
  182 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 182 213
  (Polychromatic418967fa.accept_9_3_2_6_1_264 12 182 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 182 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 182 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 182 213 (accept_3_4 10 182 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 182 213 (Polychromatic418967fa.accept_20_9_2_13_1_6778 9 182 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 182 213
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 182 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 182 213 (accept_3_4 7 182 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  182 213 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 182 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 182 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 182 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 182 213 (accept_3_4 4 182 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 182 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 182 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 182 213
  (Polychromatic418967fa.accept_11_2_6_4_1_3028 2 182 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 182 213 (accept_3_4 1 182 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 182
  213)))))))))))))))))))))))))))))))) (allB_succ' 33 181 213 (Eq.refl Bool.true) (allA_succ_of_accept 32 181 213
  (accept_3_5 32 181 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 181 213
  (Polychromatic418967fa.accept_9_4_1_6_1_284 31 181 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 181 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 181 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 181 213 (accept_3_5 29 181 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 181 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 181 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 181 213 (Polychromatic418967fa.accept_12_3_1_9_1_202
  27 181 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 181 213 (accept_3_5 26
  181 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 181 213
  (Polychromatic418967fa.accept_7_4_6_3_1_271 25 181 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 181 213 (Polychromatic418967fa.accept_14_10_13_3_1_2552 24 181 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 181 213 (accept_3_5 23 181 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 181 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 181 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 181 213
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 181 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 181 213 (accept_3_5 20 181 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 181 213 (Polychromatic418967fa.accept_13_6_12_5_1_2304 19 181 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 181 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 181 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 181 213 (accept_3_5 17 181 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 181 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 181 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 181 213
  (Polychromatic418967fa.accept_12_3_1_9_1_202 15 181 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 181 213 (accept_3_5 14 181 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 181 213 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 181 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 181 213 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 181 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 181 213 (accept_3_5 11 181 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 181 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 181 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 181 213
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 181 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 181 213 (accept_3_5 8 181 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  181 213 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 181 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 181 213 (Polychromatic418967fa.accept_13_6_12_5_1_2304 6 181 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 181 213 (accept_3_5 5 181 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 181 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 181 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 181 213
  (Polychromatic418967fa.accept_9_3_1_6_1_86 3 181 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 181 213 (accept_3_5 2 181 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  181 213 (Polychromatic418967fa.accept_13_1_12_5_1_1601 1 181 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 181 213))))))))))))))))))))))))))))))))) (allB_succ' 34 180 213 (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 180 213 3 11 60 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 180 213 (Polychromatic418967fa.accept_13_6_11_5_1_133 32 180 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 180 213
  (Polychromatic418967fa.accept_16_15_4_5_1_1411 31 180 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 180 213 3 10 60 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 180 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 180 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 180 213
  (Polychromatic418967fa.accept_16_12_4_5_1_2273 28 180 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 180 213 3 9 60 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 180 213 (Polychromatic418967fa.accept_25_1_5_13_1_12611 26 180 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 180 213 (Polychromatic418967fa.accept_8_1_4_5_1_48 25
  180 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 180 213 3 8 60 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 180 213
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 180 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 180 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 180 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 180 213 3 7 60 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 180 213 (Polychromatic418967fa.accept_13_7_11_5_1_2302
  20 180 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 180 213
  (Polychromatic418967fa.accept_13_6_11_5_1_133 19 180 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 180 213 3 6 60 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 180 213 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 180 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 180 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 180 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 180 213 3 5 60 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 180 213
  (Polychromatic418967fa.accept_19_14_9_4_1_7029 14 180 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 180 213 (Polychromatic418967fa.accept_17_13_10_9_1_946 13 180 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 180 213 3 4 60 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 180 213
  (Polychromatic418967fa.accept_21_11_12_3_1_6461 11 180 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 180 213 (Polychromatic418967fa.accept_19_10_9_4_1_5620 10 180 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 180 213 3 3 60 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 180 213
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 180 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 180 213 (Polychromatic418967fa.accept_13_7_11_5_1_2302 7 180 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 180 213 3 2 60 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 180 213 (Polychromatic418967fa.accept_14_5_12_3_1_3397 5 180 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 180 213
  (Polychromatic418967fa.accept_21_4_12_3_1_12610 4 180 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 180 213 3 1 60 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 180 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 180 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 180 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 180 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180 213))))))))))))))))))))))))))))))))))
  (allB_succ' 35 179 213 (Eq.refl Bool.true) (allA_succ_of_accept 34 179 213 (accept_3_4 34 179 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 179 213 (Polychromatic418967fa.accept_19_14_8_4_1_2961 33 179 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 179 213
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 179 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 179 213 (accept_3_4 31 179 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 179 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 179 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 179 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 179 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 179 213 (accept_3_4 28 179 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 179 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 179 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 179 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 179 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 179 213 (accept_3_4 25 179 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 179 213 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 179 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 179 213 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 179 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 179 213 (accept_3_4 22 179 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 179 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 179 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 179 213
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 179 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 179 213 (accept_3_4 19 179 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 179 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 179 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 179 213 (Polychromatic418967fa.accept_13_4_10_5_1_1644 17 179 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 179 213 (accept_3_4 16 179 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 179 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 179 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 179 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 179 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 179 213 (accept_3_4 13 179 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 179 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 179 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 179 213 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 179 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 179 213 (accept_3_4 10 179 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 179 213 (Polychromatic418967fa.accept_18_9_17_15_1_2267 9 179 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 179 213
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 179 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 179 213 (accept_3_4 7 179 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  179 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 179 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 179 213 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 179 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 179 213 (accept_3_4 4 179 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 179 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 179 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 179 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 179 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 179 213 (accept_3_4 1 179 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 179
  213))))))))))))))))))))))))))))))))))) (allB_succ' 36 178 213 (Eq.refl Bool.true) (allA_succ_of_accept 35 178 213
  (accept_3_5 35 178 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 178 213
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 34 178 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 178 213 (Polychromatic418967fa.accept_17_16_8_9_1_1772 33 178 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 178 213 (accept_3_5 32 178 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 178 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 178 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 178 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 30
  178 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 178 213 (accept_3_5 29
  178 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 178 213
  (Polychromatic418967fa.accept_9_1_7_6_1_75 28 178 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 178 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 178 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 178 213 (accept_3_5 26 178 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 178 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 178 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 178 213 (Polychromatic418967fa.accept_15_9_13_3_1_535
  24 178 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 178 213 (accept_3_5 23
  178 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 178 213
  (Polychromatic418967fa.accept_9_4_7_6_1_255 22 178 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 178 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 178 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 178 213 (accept_3_5 20 178 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 178 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 178 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 178 213 (Polychromatic418967fa.accept_12_6_10_9_1_531
  18 178 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 178 213 (accept_3_5 17
  178 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 178 213
  (Polychromatic418967fa.accept_10_6_8_3_1_930 16 178 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 178 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 178 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 178 213 (accept_3_5 14 178 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 178 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 178 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 178 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 12
  178 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 178 213 (accept_3_5 11
  178 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 178 213
  (Polychromatic418967fa.accept_9_1_7_6_1_75 10 178 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 178 213 (Polychromatic418967fa.accept_11_9_2_4_1_707 9 178 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 178 213 (accept_3_5 8 178 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 178 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 178 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 178 213 (Polychromatic418967fa.accept_10_6_8_3_1_930 6
  178 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 178 213 (accept_3_5 5 178
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 178 213
  (Polychromatic418967fa.accept_9_4_7_6_1_255 4 178 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 178 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 178 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 178 213 (accept_3_5 2 178 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 178 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 178 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 178 213)))))))))))))))))))))))))))))))))))) (allB_succ' 37 177 213
  (Eq.refl Bool.true) (allA_succ_of_gcd 36 177 213 3 12 59 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 177 213 (Polychromatic418967fa.accept_10_5_7_3_1_561 35 177 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 177 213
  (Polychromatic418967fa.accept_7_6_2_3_1_107 34 177 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 177 213 3 11 59 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 177 213 (Polychromatic418967fa.accept_15_2_12_3_1_1183 32 177 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 177 213
  (Polychromatic418967fa.accept_16_15_1_5_1_2265 31 177 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 177 213 3 10 59 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 177 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 177 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 177 213 (Polychromatic418967fa.accept_8_4_1_5_1_186
  28 177 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 177 213 3 9 59 71
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 177 213
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 177 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 177 213 (Polychromatic418967fa.accept_10_5_7_3_1_561 25 177 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 177 213 3 8 59 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 177 213 (Polychromatic418967fa.accept_13_10_8_5_1_1616
  23 177 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 177 213
  (Polychromatic418967fa.accept_7_1_2_3_1_257 22 177 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 177 213 3 7 59 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 177 213 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 177 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 177 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 177 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 177 213 3 6 59 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 177 213
  (Polychromatic418967fa.accept_15_2_12_3_1_1183 17 177 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 177 213 (Polychromatic418967fa.accept_10_6_7_3_1_547 16 177 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 177 213 3 5 59 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 177 213 (Polychromatic418967fa.accept_10_4_7_3_1_54 14
  177 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 177 213
  (Polychromatic418967fa.accept_7_6_2_3_1_107 13 177 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 177 213 3 4 59 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 177 213 (Polychromatic418967fa.accept_22_11_1_15_1_11044 11 177 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 177 213
  (Polychromatic418967fa.accept_13_10_8_5_1_1616 10 177 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 177 213 3 3 59 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 177 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 177 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 213 (Polychromatic418967fa.accept_15_7_12_3_1_1137 7 177
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 177 213 3 2 59 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 177 213
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 177 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 177 213 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 177 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 177 213 3 1 59 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 177 213 (Polychromatic418967fa.accept_15_2_12_3_1_1183 2 177 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 213
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 177 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 177 213))))))))))))))))))))))))))))))))))))) (allB_succ' 38 176 213 (Eq.refl Bool.true) (allA_succ_of_accept
  37 176 213 (accept_3_4 37 176 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 176 213
  (Polychromatic418967fa.accept_15_6_11_3_1_1172 36 176 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 176 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 176 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 176 213 (accept_3_4 34 176 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 176 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 176 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 176 213 (Polychromatic418967fa.accept_7_4_1_3_1_277
  32 176 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 176 213 (accept_3_4 31
  176 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 176 213
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 176 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 176 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 176 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 176 213 (accept_3_4 28 176 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 176 213 (Polychromatic418967fa.accept_10_7_6_3_1_927 27 176 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 176 213
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 176 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 176 213 (accept_3_4 25 176 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 176 213 (Polychromatic418967fa.accept_13_11_7_5_1_2314 24 176 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 176 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 176 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 176 213 (accept_3_4 22 176 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 176 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 176 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 176 213
  (Polychromatic418967fa.accept_9_2_5_6_1_536 20 176 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 176 213 (accept_3_4 19 176 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 176 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 176 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 176 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 176 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 176 213 (accept_3_4 16 176 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 176 213 (Polychromatic418967fa.accept_13_2_7_5_1_3189 15 176 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 176 213
  (Polychromatic418967fa.accept_15_14_11_3_1_1957 14 176 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 176 213 (accept_3_4 13 176 213 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 176 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 176 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 176 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 176 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 176 213 (accept_3_4 10 176 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 176 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 9
  176 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 176 213
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 176 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 176 213 (accept_3_4 7 176 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  176 213 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 176 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 176 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 176 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 176 213 (accept_3_4 4 176 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 176 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 176 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 176 213
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 176 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 176 213 (accept_3_4 1 176 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 176
  213)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 175 213 (Eq.refl Bool.true) (allA_succ_of_accept 38 175 213
  (accept_3_5 38 175 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 175 213
  (Polychromatic418967fa.accept_9_1_4_6_1_5 37 175 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 175 213 (Polychromatic418967fa.accept_13_10_6_5_1_2297 36 175 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 175 213 (accept_3_5 35 175 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 175 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 175 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 175 213 (Polychromatic418967fa.accept_16_1_15_5_1_708
  33 175 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 175 213 (accept_3_5 32
  175 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 175 213
  (Polychromatic418967fa.accept_17_14_5_9_1_7766 31 175 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 175 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 175 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 175 213 (accept_3_5 29 175 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 175 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 175 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 175 213 (Polychromatic418967fa.accept_10_7_5_3_1_542
  27 175 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 175 213 (accept_3_5 26
  175 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 175 213
  (Polychromatic418967fa.accept_9_7_4_6_1_273 25 175 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 175 213 (Polychromatic418967fa.accept_13_11_6_5_1_2339 24 175 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 175 213 (accept_3_5 23 175 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 175 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 175 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 175 213 (Polychromatic418967fa.accept_9_3_4_6_1_252
  21 175 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 175 213 (accept_3_5 20
  175 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 175 213
  (Polychromatic418967fa.accept_9_1_4_6_1_5 19 175 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 175 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 175 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 175 213 (accept_3_5 17 175 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 175 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 175 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 175 213 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  15 175 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 175 213 (accept_3_5 14
  175 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 175 213
  (Polychromatic418967fa.accept_15_13_10_3_1_1952 13 175 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 175 213 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 175 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 175 213 (accept_3_5 11 175 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 175 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 175 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 175 213
  (Polychromatic418967fa.accept_15_9_10_3_1_2845 9 175 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 175 213 (accept_3_5 8 175 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  175 213 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 175 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 175 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 175 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 175 213 (accept_3_5 5 175 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 175 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 175 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 175 213
  (Polychromatic418967fa.accept_9_3_4_6_1_252 3 175 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 175 213 (accept_3_5 2 175 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  175 213 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 175 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 175 213))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 174 213 (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 174 213 3 13 58 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 174 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 38 174 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 174 213 (Polychromatic418967fa.accept_7_2_6_3_1_100
  37 174 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 174 213 3 12 58 71
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 174 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 174 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 174 213 (Polychromatic418967fa.accept_9_7_3_6_1_270 34 174 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 174 213 3 11 58 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 174 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 32
  174 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 174 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 174 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 174 213 3 10 58 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 174 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 174 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 174 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 28
  174 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 174 213 3 9 58 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 174 213
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 174 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 174 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 174 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 174 213 3 8 58 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 174 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 23
  174 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 174 213
  (Polychromatic418967fa.accept_9_4_3_6_1_532 22 174 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 174 213 3 7 58 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 174 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 174 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 174 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 174 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 174 213 3 6 58 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 174 213
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 174 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 174 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 174 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 174 213 3 5 58 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 174 213 (Polychromatic418967fa.accept_9_5_3_6_1_269 14
  174 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 174 213
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 174 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 174 213 3 4 58 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 174 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 174 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 174 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 174 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 174 213 3 3 58 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 174 213
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 174 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 174 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 174 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 174 213 3 2 58 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 174 213 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 174 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 174 213
  (Polychromatic418967fa.accept_7_4_6_3_1_271 4 174 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 174 213 3 1 58 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 174 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 174 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 174 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 174 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174 213))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 41 173 213 (Eq.refl Bool.true) (allA_succ_of_accept 40 173 213 (accept_3_4 40 173 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 173 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 173 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 173 213
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 173 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 173 213 (accept_3_4 37 173 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 173 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 173 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 173 213 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 173 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 173 213 (accept_3_4 34 173 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 173 213 (Polychromatic418967fa.accept_16_1_13_5_1_2280 33 173 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 173 213
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 173 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 173 213 (accept_3_4 31 173 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 173 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 173 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 173 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 173 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 173 213 (accept_3_4 28 173 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 173 213 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 173 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 173 213
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 173 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 173 213 (accept_3_4 25 173 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 173 213 (Polychromatic418967fa.accept_15_9_8_3_1_557 24 173 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 173 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 173 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 173 213 (accept_3_4 22 173 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 173 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 173 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 173 213
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 173 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 173 213 (accept_3_4 19 173 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 173 213 (Polychromatic418967fa.accept_11_7_8_4_1_718 18 173 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 173 213 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 173 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 173 213 (accept_3_4 16 173 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 173 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 173 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 173 213
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 173 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 173 213 (accept_3_4 13 173 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 173 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 173 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 173 213 (Polychromatic418967fa.accept_15_11_8_3_1_1943 11 173 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 173 213 (accept_3_4 10 173 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 173 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 173 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 173 213
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 173 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 173 213 (accept_3_4 7 173 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  173 213 (Polychromatic418967fa.accept_13_6_4_5_1_2330 6 173 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 173 213 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 173 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 173 213 (accept_3_4 4 173 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 173 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 173 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 173 213
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 173 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 173 213 (accept_3_4 1 173 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 173
  213))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 172 213 (Eq.refl Bool.true) (allA_succ_of_accept 41 172
  213 (accept_3_5 41 172 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 172 213
  (Polychromatic418967fa.accept_9_4_1_6_1_284 40 172 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 172 213 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 172 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 172 213 (accept_3_5 38 172 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 172 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 172 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 172 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 36
  172 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 172 213 (accept_3_5 35
  172 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 172 213
  (Polychromatic418967fa.accept_7_6_4_3_1_266 34 172 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 172 213 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 172 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 172 213 (accept_3_5 32 172 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 172 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 172 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 172 213 (Polychromatic418967fa.accept_9_3_1_6_1_86 30
  172 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 172 213 (accept_3_5 29
  172 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 172 213
  (Polychromatic418967fa.accept_13_2_3_5_1_2294 28 172 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 172 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 172 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 172 213 (accept_3_5 26 172 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 172 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 172 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 172 213 (Polychromatic418967fa.accept_13_11_3_5_1_982
  24 172 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 172 213 (accept_3_5 23
  172 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 172 213
  (Polychromatic418967fa.accept_7_1_4_3_1_21 22 172 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 172 213 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 172 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 172 213 (accept_3_5 20 172 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 172 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 172 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 172 213 (Polychromatic418967fa.accept_12_6_4_9_1_544
  18 172 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 172 213 (accept_3_5 17
  172 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 172 213
  (Polychromatic418967fa.accept_9_7_1_6_1_261 16 172 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 172 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 172 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 172 213 (accept_3_5 14 172 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 172 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 172 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 172 213 (Polychromatic418967fa.accept_9_3_1_6_1_86 12
  172 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 172 213 (accept_3_5 11
  172 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 172 213
  (Polychromatic418967fa.accept_15_10_7_3_1_1939 10 172 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 172 213 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 172 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 172 213 (accept_3_5 8 172 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 172 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 172 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 172 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 6
  172 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 172 213 (accept_3_5 5 172
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 172 213
  (Polychromatic418967fa.accept_9_4_1_6_1_284 4 172 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 172 213 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 172 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 172 213 (accept_3_5 2 172 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 172 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 172 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 172 213)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43
  171 213 (Eq.refl Bool.true) (allA_succ_of_gcd 42 171 213 3 14 57 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 171 213 (Polychromatic418967fa.accept_12_5_3_9_1_541 41 171 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 171 213
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 40 171 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 171 213 3 13 57 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 171 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 171 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 171 213 (Polychromatic418967fa.accept_12_1_3_9_1_174
  37 171 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 171 213 3 12 57 71
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 171 213
  (Polychromatic418967fa.accept_11_2_6_4_1_3028 35 171 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 171 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 171 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 171 213 3 11 57 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 171 213 (Polychromatic418967fa.accept_10_2_1_3_1_233
  32 171 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 171 213
  (Polychromatic418967fa.accept_12_7_3_9_1_999 31 171 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 171 213 3 10 57 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 171 213 (Polychromatic418967fa.accept_12_5_3_9_1_541 29 171 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 171 213 (Polychromatic418967fa.accept_10_8_1_3_1_1374
  28 171 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 171 213 3 9 57 71
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 171 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 171 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 171 213 (Polychromatic418967fa.accept_12_1_3_9_1_174 25 171 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 171 213 3 8 57 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 171 213 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  23 171 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 171 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 171 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 171 213 3 7 57 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 171 213 (Polychromatic418967fa.accept_13_7_2_5_1_2344 20 171 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 171 213 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 171
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 171 213 3 6 57 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 171 213
  (Polychromatic418967fa.accept_12_5_3_9_1_541 17 171 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 171 213 (Polychromatic418967fa.accept_13_3_2_5_1_1632 16 171 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 171 213 3 5 57 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 171 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 14
  171 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 213
  (Polychromatic418967fa.accept_11_2_6_4_1_3028 13 171 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 171 213 3 4 57 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 171 213 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 171 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 171 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 171 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 171 213 3 3 57 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 171 213
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 8 171 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 171 213 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 171 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 171 213 3 2 57 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 171 213 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 171 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 171 213
  (Polychromatic418967fa.accept_13_4_2_5_1_4045 4 171 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 171 213 3 1 57 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 171 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 171 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 213 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 171 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 171
  213))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 170 213 (Eq.refl Bool.true) (allA_succ_of_accept 43 170
  213 (accept_3_4 43 170 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 170 213
  (Polychromatic418967fa.accept_12_6_2_9_1_537 42 170 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 170 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 170 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 170 213 (accept_3_4 40 170 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 170 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 170 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 170 213 (Polychromatic418967fa.accept_9_2_8_6_1_79 38
  170 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 170 213 (accept_3_4 37
  170 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 170 213
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 170 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 170 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 170 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 170 213 (accept_3_4 34 170 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 170 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 170 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 170 213 (Polychromatic418967fa.accept_9_5_8_6_1_281
  32 170 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 170 213 (accept_3_4 31
  170 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 170 213
  (Polychromatic418967fa.accept_9_3_8_6_1_80 30 170 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 170 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 170 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 170 213 (accept_3_4 28 170 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 170 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 170 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 170 213 (Polychromatic418967fa.accept_7_5_2_3_1_106
  26 170 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 170 213 (accept_3_4 25
  170 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 170 213
  (Polychromatic418967fa.accept_15_9_5_3_1_554 24 170 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 170 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 170 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 170 213 (accept_3_4 22 170 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 170 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 170 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 170 213 (Polychromatic418967fa.accept_7_6_2_3_1_107
  20 170 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 170 213 (accept_3_4 19
  170 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 170 213
  (Polychromatic418967fa.accept_12_6_2_9_1_537 18 170 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 170 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 170 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 170 213 (accept_3_4 16 170 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 170 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 170 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 170 213 (Polychromatic418967fa.accept_9_5_8_6_1_281
  14 170 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 170 213 (accept_3_4 13
  170 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 170 213
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 170 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 170 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 170 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 170 213 (accept_3_4 10 170 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 170 213 (Polychromatic418967fa.accept_13_9_1_5_1_964 9 170 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 170 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 8
  170 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 170 213 (accept_3_4 7 170
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 170 213
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 170 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 170 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 170 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 170 213 (accept_3_4 4 170 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 170 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 170 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 170 213 (Polychromatic418967fa.accept_9_2_8_6_1_79 2
  170 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 170 213 (accept_3_4 1 170
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170 213)))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  45 169 213 (Eq.refl Bool.true) (allA_succ_of_accept 44 169 213 (accept_3_5 44 169 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 169 213 (Polychromatic418967fa.accept_16_11_9_5_1_4412 43 169 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 169 213
  (Polychromatic418967fa.accept_17_8_16_9_1_8952 42 169 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 169 213 (accept_3_5 41 169 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 169 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 169 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 169 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 169 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 169 213 (accept_3_5 38 169 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 169 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 169 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 169 213
  (Polychromatic418967fa.accept_8_4_1_5_1_186 36 169 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 169 213 (accept_3_5 35 169 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 169 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 169 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 169 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 169 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 169 213 (accept_3_5 32 169 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 169 213 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 169 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 169 213
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 169 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 169 213 (accept_3_5 29 169 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 169 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 169 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 169 213 (Polychromatic418967fa.accept_12_3_1_9_1_202 27 169 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 169 213 (accept_3_5 26 169 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 169 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 169 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 169 213
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 169 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 169 213 (accept_3_5 23 169 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 169 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 169 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 169 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 169 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 169 213 (accept_3_5 20 169 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 169 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 169 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 169 213
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 169 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 169 213 (accept_3_5 17 169 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 169 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 169 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 169 213 (Polychromatic418967fa.accept_12_3_1_9_1_202 15 169 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 169 213 (accept_3_5 14 169 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 169 213 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 169 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 169 213
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 169 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 169 213 (accept_3_5 11 169 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 169 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 169 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 169 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 169 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 169 213 (accept_3_5 8 169 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 169 213 (Polychromatic418967fa.accept_15_7_4_3_1_1930 7 169 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 169 213
  (Polychromatic418967fa.accept_10_6_9_3_1_935 6 169 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 169 213 (accept_3_5 5 169 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  169 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 169 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 169 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 169 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 169 213 (accept_3_5 2 169 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 169 213 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 169 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 169 213)))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 46 168 213 (Eq.refl Bool.true) (allA_succ_of_gcd 45 168 213 3 15 56 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 168 213
  (Polychromatic418967fa.accept_16_12_8_5_1_3316 44 168 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 168 213 (Polychromatic418967fa.accept_13_4_12_5_1_476 43 168 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 168 213 3 14 56 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 168 213 (Polychromatic418967fa.accept_10_1_8_3_1_947
  41 168 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 168 213
  (Polychromatic418967fa.accept_11_7_3_4_1_729 40 168 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 168 213 3 13 56 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 168 213 (Polychromatic418967fa.accept_20_18_8_13_1_6761 38 168 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 168 213
  (Polychromatic418967fa.accept_25_12_18_13_1_12609 37 168 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 168 213 3 12 56 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 168 213 (Polychromatic418967fa.accept_10_5_8_3_1_229 35 168 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 168 213
  (Polychromatic418967fa.accept_13_8_12_5_1_1604 34 168 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 168 213 3 11 56 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 168 213 (Polychromatic418967fa.accept_13_6_12_5_1_2304 32 168 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 168 213
  (Polychromatic418967fa.accept_10_1_8_3_1_947 31 168 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 168 213 3 10 56 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 168 213 (Polychromatic418967fa.accept_11_7_3_4_1_729 29 168 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 168 213
  (Polychromatic418967fa.accept_13_2_12_5_1_1602 28 168 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 168 213 3 9 56 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 168 213 (Polychromatic418967fa.accept_10_6_8_3_1_930 26 168 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 168 213 (Polychromatic418967fa.accept_10_5_8_3_1_229 25 168
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 168 213 3 8 56 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 168 213
  (Polychromatic418967fa.accept_17_6_15_9_1_1791 23 168 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 168 213 (Polychromatic418967fa.accept_18_4_6_15_1_2250 22 168 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 168 213 3 7 56 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 168 213 (Polychromatic418967fa.accept_13_7_12_5_1_1603
  20 168 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 168 213
  (Polychromatic418967fa.accept_13_6_12_5_1_2304 19 168 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 168 213 3 6 56 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 168 213 (Polychromatic418967fa.accept_13_4_12_5_1_476 17 168 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 168 213 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 168
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 168 213 3 5 56 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 168 213
  (Polychromatic418967fa.accept_13_1_12_5_1_1601 14 168 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 168 213 (Polychromatic418967fa.accept_16_13_8_5_1_3298 13 168 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 168 213 3 4 56 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 168 213 (Polychromatic418967fa.accept_10_1_8_3_1_947
  11 168 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 168 213
  (Polychromatic418967fa.accept_18_10_6_15_1_3412 10 168 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 168 213 3 3 56 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 168 213 (Polychromatic418967fa.accept_13_8_12_5_1_1604 8 168 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 168 213 (Polychromatic418967fa.accept_11_7_3_4_1_729 7
  168 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 168 213 3 2 56 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 168 213
  (Polychromatic418967fa.accept_10_5_8_3_1_229 5 168 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 168 213 (Polychromatic418967fa.accept_13_4_12_5_1_476 4 168 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 168 213 3 1 56 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 168 213 (Polychromatic418967fa.accept_13_2_12_5_1_1602 2 168 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 168 213
  (Polychromatic418967fa.accept_10_1_8_3_1_947 1 168 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 168 213)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 167 213 (Eq.refl Bool.true)
  (allA_succ_of_accept 46 167 213 (accept_3_4 46 167 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 167 213 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 167 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 167 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 167 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 167 213 (accept_3_4 43 167 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 167 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 167 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 167 213
  (Polychromatic418967fa.accept_26_15_11_5_1_12608 41 167 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 167 213 (accept_3_4 40 167 213 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 167 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 167 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 167 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 167 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 167 213 (accept_3_4 37 167 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 167 213 (Polychromatic418967fa.accept_10_6_7_3_1_547
  36 167 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 167 213
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 167 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 167 213 (accept_3_4 34 167 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 167 213 (Polychromatic418967fa.accept_13_7_11_5_1_2302 33 167 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 167 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 167 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 167 213 (accept_3_4 31 167 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 167 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 167 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 167 213
  (Polychromatic418967fa.accept_9_2_5_6_1_536 29 167 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 167 213 (accept_3_4 28 167 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 167 213 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 167 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 167 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 167 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 167 213 (accept_3_4 25 167 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 167 213 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 167 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 167 213
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 167 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 167 213 (accept_3_4 22 167 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 167 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 167 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 167 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 167 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 167 213 (accept_3_4 19 167 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 167 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 167 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 167 213
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 167 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 167 213 (accept_3_4 16 167 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 167 213 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 167 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 167 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 167 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 167 213 (accept_3_4 13 167 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 167 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 167 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 167 213
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 167 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 167 213 (accept_3_4 10 167 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  167 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 167 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 167 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 167 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 167 213 (accept_3_4 7 167 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 167 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 167 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 167 213
  (Polychromatic418967fa.accept_10_5_7_3_1_561 5 167 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 167 213 (accept_3_4 4 167 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  167 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 167 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 167 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 167 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 167 213 (accept_3_4 1 167 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 167 213))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 166 213 (Eq.refl
  Bool.true) (allA_succ_of_accept 47 166 213 (accept_3_5 47 166 213 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 166 213 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 166 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 166 213 (Polychromatic418967fa.accept_13_6_10_5_1_1648 45 166
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 166 213 (accept_3_5 44 166
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 166 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 166 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 166 213 (Polychromatic418967fa.accept_12_6_10_9_1_531 42 166 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 166 213 (accept_3_5 41 166 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 166 213 (Polychromatic418967fa.accept_19_2_14_4_1_4195 40 166 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 166 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 166 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 166 213 (accept_3_5 38 166 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 166 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 166 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 166 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 166 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 166 213 (accept_3_5 35 166 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 166 213 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 166 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 166 213
  (Polychromatic418967fa.accept_14_5_12_3_1_3397 33 166 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 166 213 (accept_3_5 32 166 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 166 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 166 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 166 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 166 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 166 213 (accept_3_5 29 166 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 166 213 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 166 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 166 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 166 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 166 213 (accept_3_5 26 166 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 166 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 166 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 166 213 (Polychromatic418967fa.accept_18_6_4_15_1_2276 24 166 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 166 213 (accept_3_5 23 166 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 166 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 166 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 166 213
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 166 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 166 213 (accept_3_5 20 166 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 166 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 166 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 166 213 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 166 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 166 213 (accept_3_5 17 166 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 166 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 166 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 166 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 166 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 166 213 (accept_3_5 14 166 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 166 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 166 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 166 213 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 166 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 166 213 (accept_3_5 11 166 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 166 213 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 166 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 166 213
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 166 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 166 213 (accept_3_5 8 166 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  166 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 166 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 166 213 (Polychromatic418967fa.accept_12_6_10_9_1_531 6 166 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 166 213 (accept_3_5 5 166 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 166 213 (Polychromatic418967fa.accept_13_4_10_5_1_1644 4 166 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 166 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 166 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 166 213 (accept_3_5 2 166 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  166 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 166 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 166 213)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 165 213 (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 165 213 3 16 55 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 165 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 165 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 165 213
  (Polychromatic418967fa.accept_9_1_3_6_1_70 46 165 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 165 213 3 15 55 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 165 213 (Polychromatic418967fa.accept_9_8_3_6_1_533 44 165 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 165 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 43
  165 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 165 213 3 14 55 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 165 213
  (Polychromatic418967fa.accept_7_6_4_3_1_266 41 165 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 165 213 (Polychromatic418967fa.accept_9_4_3_6_1_532 40 165 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 165 213 3 13 55 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 165 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 38
  165 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 165 213
  (Polychromatic418967fa.accept_9_1_3_6_1_70 37 165 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 165 213 3 12 55 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 165 213 (Polychromatic418967fa.accept_9_8_3_6_1_533 35 165 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 165 213 (Polychromatic418967fa.accept_7_6_4_3_1_266
  34 165 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 165 213 3 11 55 71
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 165 213
  (Polychromatic418967fa.accept_9_5_3_6_1_269 32 165 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 165 213 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 165 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 165 213 3 10 55 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 165 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 29
  165 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 165 213
  (Polychromatic418967fa.accept_9_1_3_6_1_70 28 165 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 165 213 3 9 55 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 165 213 (Polychromatic418967fa.accept_9_8_3_6_1_533 26 165 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 165 213 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 165 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 165 213 3 8 55 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 165 213
  (Polychromatic418967fa.accept_9_5_3_6_1_269 23 165 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 165 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 165 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 165 213 3 7 55 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 165 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 20
  165 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 165 213
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 165 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 165 213 3 6 55 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 165 213 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 165 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 165 213 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 165 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 165 213 3 5 55 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 165 213
  (Polychromatic418967fa.accept_9_5_3_6_1_269 14 165 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 165 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 165 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 165 213 3 4 55 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 165 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 11
  165 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 165 213
  (Polychromatic418967fa.accept_9_1_3_6_1_70 10 165 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 165 213 3 3 55 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 165 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 165 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 213 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 165 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 165 213 3 2 55 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 165 213
  (Polychromatic418967fa.accept_9_5_3_6_1_269 5 165 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 165 213 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 165 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 165 213 3 1 55 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 165 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 165 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 213
  (Polychromatic418967fa.accept_7_1_4_3_1_21 1 165 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 165 213))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 164 213 (Eq.refl Bool.true)
  (allA_succ_of_accept 49 164 213 (accept_3_4 49 164 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 164 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 164 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 164 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 164 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 164 213 (accept_3_4 46 164 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 164 213 (Polychromatic418967fa.accept_19_7_12_4_1_8522 45 164 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 164 213
  (Polychromatic418967fa.accept_9_8_2_6_1_875 44 164 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 164 213 (accept_3_4 43 164 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 164 213 (Polychromatic418967fa.accept_12_6_8_9_1_553 42 164 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 164 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 164 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 164 213 (accept_3_4 40 164 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 164 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 164 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 164 213
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 38 164 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 164 213 (accept_3_4 37 164 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 164 213 (Polychromatic418967fa.accept_13_10_8_5_1_1616 36 164 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 164 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 164 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 164 213 (accept_3_4 34 164 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 164 213 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 164 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 164 213
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 164 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 164 213 (accept_3_4 31 164 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 164 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 164 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 164 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 164 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 164 213 (accept_3_4 28 164 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 164 213 (Polychromatic418967fa.accept_10_7_4_3_1_560 27 164 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 164 213
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 164 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 164 213 (accept_3_4 25 164 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 164 213 (Polychromatic418967fa.accept_16_8_4_5_1_4379 24 164 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 164 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 164 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 164 213 (accept_3_4 22 164 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 164 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 164 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 164 213
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 20 164 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 164 213 (accept_3_4 19 164 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 164 213 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 164 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 164 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 164 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 164 213 (accept_3_4 16 164 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 164 213 (Polychromatic418967fa.accept_16_15_4_5_1_1411 15 164 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 164 213
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 164 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 164 213 (accept_3_4 13 164 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 164 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 164 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 164 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 164 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 164 213 (accept_3_4 10 164 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 164 213 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 164 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 164 213
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 164 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 164 213 (accept_3_4 7 164 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  164 213 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 164 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 164 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 164 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 164 213 (accept_3_4 4 164 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 164 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 164 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 164 213
  (Polychromatic418967fa.accept_15_2_14_3_1_1916 2 164 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 164 213 (accept_3_4 1 164 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 164
  213)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 163 213 (Eq.refl Bool.true) (allA_succ_of_accept
  50 163 213 (accept_3_5 50 163 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 163 213
  (Polychromatic418967fa.accept_9_4_1_6_1_284 49 163 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 163 213 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 163 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 163 213 (accept_3_5 47 163 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 163 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 163 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 163 213
  (Polychromatic418967fa.accept_19_7_11_4_1_1872 45 163 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 163 213 (accept_3_5 44 163 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 163 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 163 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 163 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 163 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 163 213 (accept_3_5 41 163 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 163 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 163 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 163 213
  (Polychromatic418967fa.accept_9_3_1_6_1_86 39 163 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 163 213 (accept_3_5 38 163 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 163 213 (Polychromatic418967fa.accept_13_11_7_5_1_2314 37 163 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 163 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 163 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 163 213 (accept_3_5 35 163 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 163 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 163 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 163 213
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 163 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 163 213 (accept_3_5 32 163 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 163 213 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 163 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 163 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 163 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 163 213 (accept_3_5 29 163 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 163 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 163 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 163 213
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 163 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 163 213 (accept_3_5 26 163 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 163 213 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 163 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 163 213 (Polychromatic418967fa.accept_11_2_9_4_1_310 24 163 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 163 213 (accept_3_5 23 163 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 163 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 163 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 163 213
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 163 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 163 213 (accept_3_5 20 163 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 163 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 163 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 163 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 163 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 163 213 (accept_3_5 17 163 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 163 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 163 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 163 213
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 163 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 163 213 (accept_3_5 14 163 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 163 213 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 163 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 163 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 163 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 163 213 (accept_3_5 11 163 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 163 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 163 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 163 213
  (Polychromatic418967fa.accept_15_9_13_3_1_535 9 163 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 163 213 (accept_3_5 8 163 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  163 213 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 163 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 163 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 163 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 163 213 (accept_3_5 5 163 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 163 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 163 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 163 213
  (Polychromatic418967fa.accept_9_3_1_6_1_86 3 163 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 163 213 (accept_3_5 2 163 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  163 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 163 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 163 213))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 162 213 (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 162 213 3 17 54 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 50 162 213 (Polychromatic418967fa.accept_12_2_6_9_1_19 50 162 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 162 213
  (Polychromatic418967fa.accept_13_10_6_5_1_2297 49 162 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 162 213 3 16 54 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 162 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 162 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 162 213 (Polychromatic418967fa.accept_7_4_1_3_1_277
  46 162 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 162 213 3 15 54 71
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 162 213
  (Polychromatic418967fa.accept_7_2_1_3_1_102 44 162 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 162 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 162 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 162 213 3 14 54 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 162 213 (Polychromatic418967fa.accept_10_1_2_3_1_1910
  41 162 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 162 213
  (Polychromatic418967fa.accept_7_5_1_3_1_103 40 162 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 162 213 3 13 54 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 162 213 (Polychromatic418967fa.accept_12_2_6_9_1_19 38 162 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 162 213 (Polychromatic418967fa.accept_7_2_1_3_1_102
  37 162 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 162 213 3 12 54 71
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 162 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 162 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 162 213 (Polychromatic418967fa.accept_11_1_8_4_1_717 34 162 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 162 213 3 11 54 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 162 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 32
  162 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 162 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 162 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 162 213 3 10 54 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 162 213 (Polychromatic418967fa.accept_11_7_8_4_1_718 29 162 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 162 213 (Polychromatic418967fa.accept_12_4_6_9_1_548
  28 162 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 162 213 3 9 54 71
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 162 213
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 162 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 162 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 162 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 162 213 3 8 54 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 162 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 23
  162 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 162 213
  (Polychromatic418967fa.accept_12_10_6_9_1_549 22 162 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 162 213 3 7 54 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 162 213 (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 162 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 162 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 162 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 162 213 3 6 54 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 162 213
  (Polychromatic418967fa.accept_13_4_6_5_1_2333 17 162 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 162 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 162 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 162 213 3 5 54 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 162 213 (Polychromatic418967fa.accept_12_2_6_9_1_19 14
  162 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 162 213
  (Polychromatic418967fa.accept_15_13_12_3_1_1180 13 162 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 162 213 3 4 54 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 162 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 162 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 162 213
  (Polychromatic418967fa.accept_12_10_6_9_1_549 10 162 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 162 213 3 3 54 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 162 213 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 162 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 162 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 162 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 162 213 3 2 54 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 162 213
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 162 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 162 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 162 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 162 213 3 1 54 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 162 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 162 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 162 213
  (Polychromatic418967fa.accept_10_1_2_3_1_1910 1 162 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 162 213)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 161 213 (Eq.refl Bool.true)
  (allA_succ_of_accept 52 161 213 (accept_3_4 52 161 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 161 213 (Polychromatic418967fa.accept_12_3_5_9_1_176 51 161 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 161 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 161 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 161 213 (accept_3_4 49 161 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 161 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 161 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 161 213
  (Polychromatic418967fa.accept_9_2_8_6_1_79 47 161 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 161 213 (accept_3_4 46 161 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 161 213 (Polychromatic418967fa.accept_16_13_1_5_1_5469 45 161 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 161 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 161 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 161 213 (accept_3_4 43 161 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 161 213 (Polychromatic418967fa.accept_10_2_1_3_1_233 42 161 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 161 213
  (Polychromatic418967fa.accept_9_5_8_6_1_281 41 161 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 161 213 (accept_3_4 40 161 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 161 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 161 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 161 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 161 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 161 213 (accept_3_4 37 161 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 161 213 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 161 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 161 213
  (Polychromatic418967fa.accept_17_1_8_9_1_1810 35 161 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 161 213 (accept_3_4 34 161 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 161 213 (Polychromatic418967fa.accept_17_16_8_9_1_1772 33 161 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 161 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 161 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 161 213 (accept_3_4 31 161 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 161 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 161 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 161 213
  (Polychromatic418967fa.accept_9_2_8_6_1_79 29 161 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 161 213 (accept_3_4 28 161 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 161 213 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 161 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 161 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 161 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 161 213 (accept_3_4 25 161 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 161 213 (Polychromatic418967fa.accept_14_10_7_3_1_1022 24 161 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 161 213
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 161 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 161 213 (accept_3_4 22 161 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 161 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 161 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 161 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 161 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 161 213 (accept_3_4 19 161 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 161 213 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 161 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 161 213
  (Polychromatic418967fa.accept_21_17_14_3_1_6411 17 161 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 161 213 (accept_3_4 16 161 213 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 161 213 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 161 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 161 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 161 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 161 213 (accept_3_4 13 161 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 161 213 (Polychromatic418967fa.accept_8_4_1_5_1_186
  12 161 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 161 213
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 161 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 161 213 (accept_3_4 10 161 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  161 213 (Polychromatic418967fa.accept_16_9_1_5_1_2282 9 161 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 161 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 161 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 161 213 (accept_3_4 7 161 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 161 213 (Polychromatic418967fa.accept_15_6_11_3_1_1172 6 161 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 161 213
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 161 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 161 213 (accept_3_4 4 161 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  161 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 161 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 161 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 161 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 161 213 (accept_3_4 1 161 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 161 213))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 160 213
  (Eq.refl Bool.true) (allA_succ_of_accept 53 160 213 (accept_3_5 53 160 213 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 160 213 (Polychromatic418967fa.accept_14_10_6_3_1_1055 52 160 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 160 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 160 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 160 213 (accept_3_5 50 160 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 160 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 49
  160 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 160 213
  (Polychromatic418967fa.accept_9_3_7_6_1_76 48 160 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 160 213 (accept_3_5 47 160 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 160 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 160 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 160 213 (Polychromatic418967fa.accept_13_6_4_5_1_2330 45 160 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 160 213 (accept_3_5 44 160 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 160 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 160 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 160 213
  (Polychromatic418967fa.accept_12_6_4_9_1_544 42 160 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 160 213 (accept_3_5 41 160 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 160 213 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 160 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 160 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 160 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 160 213 (accept_3_5 38 160 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 160 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 160 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 160 213
  (Polychromatic418967fa.accept_13_10_4_5_1_2331 36 160 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 160 213 (accept_3_5 35 160 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 160 213 (Polychromatic418967fa.accept_19_15_8_4_1_2962 34 160 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 160 213 (Polychromatic418967fa.accept_19_14_8_4_1_2961 33 160 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 160 213 (accept_3_5 32 160 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 160 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 160 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 160 213
  (Polychromatic418967fa.accept_7_2_6_3_1_100 30 160 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 160 213 (accept_3_5 29 160 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 160 213 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 160 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 160 213 (Polychromatic418967fa.accept_13_1_4_5_1_113 27 160 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 160 213 (accept_3_5 26 160 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 160 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 160 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 160 213
  (Polychromatic418967fa.accept_11_2_6_4_1_3028 24 160 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 160 213 (accept_3_5 23 160 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 160 213 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 160 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 160 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 160 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 160 213 (accept_3_5 20 160 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 160 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 160 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 160 213
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 160 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 160 213 (accept_3_5 17 160 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 160 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 160 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 160 213 (Polychromatic418967fa.accept_13_2_4_5_1_3152 15 160 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 160 213 (accept_3_5 14 160 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 160 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 160 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 160 213
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 160 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 160 213 (accept_3_5 11 160 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 160 213 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 160 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 160 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 160 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 160 213 (accept_3_5 8 160 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 160 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 160 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 160 213
  (Polychromatic418967fa.accept_12_6_4_9_1_544 6 160 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 160 213 (accept_3_5 5 160 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  160 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 160 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 160 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 160 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 160 213 (accept_3_5 2 160 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 160 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 160 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 160
  213)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 159 213 (Eq.refl Bool.true) (allA_succ_of_gcd
  54 159 213 3 18 53 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 159 213 (Polychromatic418967fa.accept_12_5_3_9_1_541 53 159 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 159 213 (Polychromatic418967fa.accept_16_4_15_5_1_5537 52 159
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 159 213 3 17 53 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 159 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 159 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 159 213 (Polychromatic418967fa.accept_12_1_3_9_1_174 49 159 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 159 213 3 16 53 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 159 213 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  47 159 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 159 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 46 159 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 159 213 3 15 53 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 159 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 159 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 159 213 (Polychromatic418967fa.accept_7_1_5_3_1_268
  43 159 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 159 213 3 14 53 71
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 159 213
  (Polychromatic418967fa.accept_12_5_3_9_1_541 41 159 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 159 213 (Polychromatic418967fa.accept_13_1_3_5_1_140 40 159 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 159 213 3 13 53 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 159 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 38
  159 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 159 213
  (Polychromatic418967fa.accept_7_2_5_3_1_98 37 159 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 159 213 3 12 53 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 159 213 (Polychromatic418967fa.accept_12_11_3_9_1_1630 35 159 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 159 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 159 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 159 213 3 11 53 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 159 213 (Polychromatic418967fa.accept_11_10_5_4_1_711 32 159 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 213
  (Polychromatic418967fa.accept_12_7_3_9_1_999 31 159 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 159 213 3 10 53 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 159 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 159 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 159 213 (Polychromatic418967fa.accept_13_2_3_5_1_2294
  28 159 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 159 213 3 9 53 71
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 159 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 159 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 159 213 (Polychromatic418967fa.accept_12_1_3_9_1_174 25 159 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 159 213 3 8 53 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 159 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 23
  159 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 159 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 159 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 159 213 3 7 53 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 159 213 (Polychromatic418967fa.accept_15_5_9_3_1_528 20 159 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 213 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 159
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 159 213 3 6 53 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 159 213
  (Polychromatic418967fa.accept_12_5_3_9_1_541 17 159 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 159 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 159 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 159 213 3 5 53 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 159 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 14
  159 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 213
  (Polychromatic418967fa.accept_12_1_3_9_1_174 13 159 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 159 213 3 4 53 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 159 213 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 159 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 159 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 159 213 3 3 53 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 159 213
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 159 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 159 213 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 159 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 159 213 3 2 53 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 159 213 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 159 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 213
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 4 159 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 159 213 3 1 53 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 159 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 159 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 159 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159
  213))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 158 213 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 158 213 (accept_3_4 55 158 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 158 213 (Polychromatic418967fa.accept_12_6_2_9_1_537 54 158 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 158 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 158 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 158 213 (accept_3_4 52 158 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 158 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 158 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 158 213
  (Polychromatic418967fa.accept_7_1_4_3_1_21 50 158 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 158 213 (accept_3_4 49 158 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 158 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 158 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 158 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 158 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 158 213 (accept_3_4 46 158 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 158 213 (Polychromatic418967fa.accept_10_5_8_3_1_229 45 158 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 158 213
  (Polychromatic418967fa.accept_9_8_5_6_1_538 44 158 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 158 213 (accept_3_4 43 158 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 158 213 (Polychromatic418967fa.accept_12_6_2_9_1_537 42 158 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 158 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 158 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 158 213 (accept_3_4 40 158 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 158 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 158 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 158 213
  (Polychromatic418967fa.accept_9_2_5_6_1_536 38 158 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 158 213 (accept_3_4 37 158 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 158 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 158 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 158 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 158 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 158 213 (accept_3_4 34 158 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 158 213 (Polychromatic418967fa.accept_13_7_2_5_1_2344 33 158 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 158 213
  (Polychromatic418967fa.accept_19_13_6_4_1_4207 32 158 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 158 213 (accept_3_4 31 158 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 158 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 158 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 158 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 158 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 158 213 (accept_3_4 28 158 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 158 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 158 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 158 213
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 158 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 158 213 (accept_3_4 25 158 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 158 213 (Polychromatic418967fa.accept_15_9_8_3_1_557 24 158 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 158 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 158 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 158 213 (accept_3_4 22 158 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 158 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 158 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 158 213
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 158 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 158 213 (accept_3_4 19 158 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 158 213 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 158 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 158 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 158 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 158 213 (accept_3_4 16 158 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 158 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 158 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 158 213
  (Polychromatic418967fa.accept_17_14_5_9_1_7766 14 158 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 158 213 (accept_3_4 13 158 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 158 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 158 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 158 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 158 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 158 213 (accept_3_4 10 158 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 158 213 (Polychromatic418967fa.accept_13_9_2_5_1_2310 9 158 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 158 213
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 158 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 158 213 (accept_3_4 7 158 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  158 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 158 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 158 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 158 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 158 213 (accept_3_4 4 158 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 158 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 158 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 158 213
  (Polychromatic418967fa.accept_9_2_5_6_1_536 2 158 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 158 213 (accept_3_4 1 158 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158
  213)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 157 213 (Eq.refl Bool.true)
  (allA_succ_of_accept 56 157 213 (accept_3_5 56 157 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 157 213 (Polychromatic418967fa.accept_9_1_4_6_1_5 55 157 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 157 213 (Polychromatic418967fa.accept_10_4_7_3_1_54 54 157 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 157 213 (accept_3_5 53 157 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 157 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 157 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 157 213
  (Polychromatic418967fa.accept_11_7_3_4_1_729 51 157 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 157 213 (accept_3_5 50 157 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 157 213 (Polychromatic418967fa.accept_15_4_7_3_1_119 49 157 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 157 213 (Polychromatic418967fa.accept_9_3_4_6_1_252 48 157 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 157 213 (accept_3_5 47 157 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 157 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 157 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 157 213
  (Polychromatic418967fa.accept_10_5_7_3_1_561 45 157 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 157 213 (accept_3_5 44 157 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 157 213 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 157 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 157 213 (Polychromatic418967fa.accept_13_3_1_5_1_499 42 157 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 157 213 (accept_3_5 41 157 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 157 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 157 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 157 213
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 157 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 157 213 (accept_3_5 38 157 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 157 213 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 157 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 157 213 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 157 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 157 213 (accept_3_5 35 157 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 157 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 157 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 157 213
  (Polychromatic418967fa.accept_16_1_13_5_1_2280 33 157 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 157 213 (accept_3_5 32 157 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 157 213 (Polychromatic418967fa.accept_17_14_4_9_1_2792 31 157 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 157 213 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 157 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 157 213 (accept_3_5 29 157 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 157 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 157 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 157 213
  (Polychromatic418967fa.accept_12_3_1_9_1_202 27 157 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 157 213 (accept_3_5 26 157 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 157 213 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 157 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 157 213 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 157 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 157 213 (accept_3_5 23 157 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 157 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 157 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 157 213
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 157 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 157 213 (accept_3_5 20 157 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 157 213 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 157 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 157 213 (Polychromatic418967fa.accept_11_7_3_4_1_729 18 157 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 157 213 (accept_3_5 17 157 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 157 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 157 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 157 213
  (Polychromatic418967fa.accept_10_5_7_3_1_561 15 157 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 157 213 (accept_3_5 14 157 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 157 213 (Polychromatic418967fa.accept_17_13_4_9_1_6390 13 157 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 157 213 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 157 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 157 213 (accept_3_5 11 157 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 157 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 157 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 213
  (Polychromatic418967fa.accept_13_9_1_5_1_964 9 157 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 157 213 (accept_3_5 8 157 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  157 213 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 157 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 157 213 (Polychromatic418967fa.accept_10_6_7_3_1_547 6 157 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 213 (accept_3_5 5 157 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 157 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 157 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 213
  (Polychromatic418967fa.accept_9_3_4_6_1_252 3 157 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 157 213 (accept_3_5 2 157 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  157 213 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 157 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 157 213)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_213_segment_001))))))))))))))))))))))))))))))))))))))))))))))))))))))))


