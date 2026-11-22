-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch270
-- name    : Polychromatic418967fa_Branch270
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:32:57.502113+00:00
-- url     : https://prove2.me/theorems/314eb693-1102-4f39-b917-b630f932e511
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch270_Segment002
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_270 : allB 270 270 :=
  allB_succ' 2 269 270 (Eq.refl Bool.true) (allA_succ_of_accept 1 269 270 (accept_3_4 1 269 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 269 270)) (allB_succ' 3 268 270 (Eq.refl Bool.true) (allA_succ_of_gcd 2 268 270 2 1 134
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 268 270
  (Polychromatic418967fa.accept_25_1_18_20_1_5828 1 268 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 268 270))) (allB_succ' 4 267 270 (Eq.refl Bool.true) (allA_succ_of_gcd 3 267 270 3 1 89 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 267 270
  (Polychromatic418967fa.accept_12_2_3_6_1_112 2 267 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 267 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 267 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 267 270)))) (allB_succ' 5 266 270 (Eq.refl Bool.true) (allA_succ_of_gcd 4
  266 270 2 2 133 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 266 270 (Polychromatic418967fa.accept_12_3_2_6_1_138 3 266 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 266 270 2 1 133 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 266 270 (accept_3_4 1 266 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 266 270))))) (allB_succ' 6 265 270 (Eq.refl Bool.true) (allA_succ_of_gcd 5 265 270 5 1
  53 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 265 270
  (Polychromatic418967fa.accept_13_4_5_10_1_1247 4 265 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 265 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 265 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 265 270 (accept_3_5 2 265 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 265 270 (Polychromatic418967fa.accept_20_1_5_10_1_3534 1 265 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 265 270)))))) (allB_succ' 7 264 270 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 264 270 6 1 44 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 264 270 (Polychromatic418967fa.accept_13_5_4_10_1_1244 5 264 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 264 270 2 2 132 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 264 270 3 1 88 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 264 270 2 1 132 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 264 270
  (Polychromatic418967fa.accept_7_1_5_4_1_134 1 264 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 264 270))))))) (allB_succ' 8 263 270 (Eq.refl Bool.true) (allA_succ_of_accept 7 263 270 (accept_3_4 7 263
  270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 263 270
  (Polychromatic418967fa.accept_13_6_3_10_1_698 6 263 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 263 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 263 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 263 270 (accept_3_4 4 263 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 263 270 (Polychromatic418967fa.accept_19_3_16_4_1_7076 3 263 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 263 270
  (Polychromatic418967fa.accept_13_2_3_10_1_658 2 263 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 263 270 (accept_3_4 1 263 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 263
  270)))))))) (allB_succ' 9 262 270 (Eq.refl Bool.true) (allA_succ_of_gcd 8 262 270 2 4 131 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 262 270
  (Polychromatic418967fa.accept_14_7_10_4_1_130 7 262 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 262 270 2 3 131 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 262 270 (accept_3_5 5 262 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 262 270 2 2 131 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 262 270 (Polychromatic418967fa.accept_11_3_9_6_1_105 3 262 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 262 270 2 1 131 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 262 270
  (Polychromatic418967fa.accept_7_1_3_4_1_128 1 262 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 262 270))))))))) (allB_succ' 10 261 270 (Eq.refl Bool.true) (allA_succ_of_gcd 9 261 270 9 1 29 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 261 270
  (Polychromatic418967fa.accept_12_8_9_6_1_127 8 261 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 261 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 261 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 261 270 3 2 87 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 261 270 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 261 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 261 270
  (Polychromatic418967fa.accept_12_4_9_6_1_440 4 261 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 261 270 3 1 87 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 261 270 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 261 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 261 270 (Polychromatic418967fa.accept_21_1_9_18_1_4428 1 261
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 261 270)))))))))) (allB_succ' 11 260 270
  (Eq.refl Bool.true) (allA_succ_of_gcd 10 260 270 10 1 26 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 260 270 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 260 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 260 270 2 4 130 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 260 270 (accept_3_4 7
  260 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 260 270 2 3 130 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 260 270 5 1 52 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 260 270 2 2 130 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 260 270
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 260 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 260 270 2 1 130 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 260 270 (accept_3_4 1 260 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 260
  270))))))))))) (allB_succ' 12 259 270 (Eq.refl Bool.true) (allA_succ_of_accept 11 259 270 (accept_3_5 11 259 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 259 270
  (Polychromatic418967fa.accept_14_10_7_4_1_3453 10 259 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 259 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 259 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 259 270 (accept_3_5 8 259 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 259 270 (Polychromatic418967fa.accept_13_7_12_10_1_640 7 259 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 259 270
  (Polychromatic418967fa.accept_13_6_12_10_1_690 6 259 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 259 270 (accept_3_5 5 259 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  259 270 (Polychromatic418967fa.accept_21_4_7_18_1_7561 4 259 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 259 270 (Polychromatic418967fa.accept_14_3_7_4_1_118 3 259 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 259 270 (accept_3_5 2 259 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 259 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 259 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 259 270)))))))))))) (allB_succ' 13 258 270 (Eq.refl
  Bool.true) (allA_succ_of_gcd 12 258 270 6 2 43 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 258 270 (Polychromatic418967fa.accept_21_11_6_18_1_4450 11 258 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 258 270 2 5 129 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 258 270 3 3 86 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 258 270 2 4 129 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 258 270
  (Polychromatic418967fa.accept_19_7_11_4_1_1872 7 258 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 258 270 6 1 43 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 258 270 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 258 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 258 270 2 2 129 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 258 270 3 1 86 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 258 270 2 1 129 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 258 270
  (Polychromatic418967fa.accept_11_1_5_6_1_397 1 258 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 258 270))))))))))))) (allB_succ' 14 257 270 (Eq.refl Bool.true) (allA_succ_of_accept 13 257 270 (accept_3_4
  13 257 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 257 270
  (Polychromatic418967fa.accept_21_12_5_18_1_7715 12 257 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 257 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 257 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 257 270 (accept_3_4 10 257 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 257 270 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 257 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 257 270
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 257 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 257 270 (accept_3_4 7 257 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  257 270 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 257 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 257 270 (Polychromatic418967fa.accept_20_5_17_10_1_3632 5 257 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 257 270 (accept_3_4 4 257 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 257 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 257 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 257 270
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 257 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 257 270 (accept_3_4 1 257 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 257
  270)))))))))))))) (allB_succ' 15 256 270 (Eq.refl Bool.true) (allA_succ_of_gcd 14 256 270 2 7 128 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 256 270
  (Polychromatic418967fa.accept_19_13_9_4_1_4309 13 256 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 256 270 2 6 128 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 256 270 (accept_3_5 11 256 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 256 270 2 5 128 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 256 270 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 256 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 256 270 2 4 128 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 256 270
  (Polychromatic418967fa.accept_21_7_4_18_1_4471 7 256 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 256 270 2 3 128 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 256 270 (accept_3_5 5 256 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 256 270 2 2 128 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 256 270 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 256 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 256 270 2 1 128 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 256 270
  (Polychromatic418967fa.accept_13_1_9_10_1_625 1 256 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 256 270))))))))))))))) (allB_succ' 16 255 270 (Eq.refl Bool.true) (allA_succ_of_gcd 15 255 270 15 1 17 18
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 255 270
  (Polychromatic418967fa.accept_12_2_3_6_1_112 14 255 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 255 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 255 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 255 270 3 4 85 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 255 270 (Polychromatic418967fa.accept_13_11_8_10_1_676
  11 255 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 255 270 5 2 51 54
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 255 270 3 3 85 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 255 270
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 255 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 255 270 (Polychromatic418967fa.accept_13_7_8_10_1_2663 7 255 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 255 270 3 2 85 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 255 270 5 1 51 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 255 270 (Polychromatic418967fa.accept_11_4_2_6_1_389 4 255 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 255 270 3 1 85 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 255 270
  (Polychromatic418967fa.accept_12_2_3_6_1_112 2 255 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 255 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 255 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 255 270)))))))))))))))) (allB_succ' 17 254 270 (Eq.refl Bool.true)
  (allA_succ_of_gcd 16 254 270 2 8 127 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 254 270 (Polychromatic418967fa.accept_12_3_2_6_1_138 15 254 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 254 270 2 7 127 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 254 270 (accept_3_4 13 254 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 254 270 2 6 127 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 254 270
  (Polychromatic418967fa.accept_17_11_16_15_1_5467 11 254 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 254 270 2 5 127 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 254 270 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 254 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 254 270 2 4 127 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 254 270 (accept_3_4 7 254 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 254 270 2 3 127 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 254 270
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 254 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 254 270 2 2 127 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 254 270 (Polychromatic418967fa.accept_12_3_2_6_1_138 3 254 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 254 270 2 1 127 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 254 270 (accept_3_4 1 254 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 254 270))))))))))))))))) (allB_succ' 18 253 270 (Eq.refl Bool.true)
  (allA_succ_of_accept 17 253 270 (accept_3_5 17 253 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 253 270 (Polychromatic418967fa.accept_13_3_6_10_1_2658 16 253 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 253 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 253 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 253 270 (accept_3_5 14 253 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 253 270 (Polychromatic418967fa.accept_19_13_6_4_1_4207 13 253 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 253 270
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 253 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 253 270 (accept_3_5 11 253 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 253 270 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 253 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 253 270 (Polychromatic418967fa.accept_13_9_6_10_1_666 9 253 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 253 270 (accept_3_5 8 253 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 253 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 253 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 253 270
  (Polychromatic418967fa.accept_25_6_3_20_1_13033 6 253 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 253 270 (accept_3_5 5 253 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  253 270 (Polychromatic418967fa.accept_13_4_6_10_1_1199 4 253 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 253 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 253 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 253 270 (accept_3_5 2 253 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 253 270 (Polychromatic418967fa.accept_16_1_13_14_1_1064 1 253 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 253 270)))))))))))))))))) (allB_succ' 19 252 270
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 252 270 18 1 14 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 252 270 (Polychromatic418967fa.accept_13_4_5_10_1_1247 17 252
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 252 270 2 8 126 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 252 270 3 5 84 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 252 270 2 7 126 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 252 270
  (Polychromatic418967fa.accept_20_13_12_10_1_3619 13 252 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 252 270 6 2 42 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 252 270 (Polychromatic418967fa.accept_24_11_12_6_1_16490 11 252 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 252 270 2 5 126 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 252 270 9 1 28 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 252 270 2 4 126 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 252 270
  (Polychromatic418967fa.accept_24_7_12_6_1_6188 7 252 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 252 270 6 1 42 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 252 270 (Polychromatic418967fa.accept_11_5_10_6_1_793 5 252 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 252 270 2 2 126 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 252 270 3 1 84 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 252 270 2 1 126 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 252 270
  (Polychromatic418967fa.accept_19_1_5_4_1_4246 1 252 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 252 270))))))))))))))))))) (allB_succ' 20 251 270 (Eq.refl Bool.true) (allA_succ_of_accept 19 251 270
  (accept_3_4 19 251 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 251 270
  (Polychromatic418967fa.accept_13_5_4_10_1_1244 18 251 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 251 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 251 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 251 270 (accept_3_4 16 251 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 251 270 (Polychromatic418967fa.accept_20_15_11_10_1_5071 15 251 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 251 270
  (Polychromatic418967fa.accept_11_3_9_6_1_105 14 251 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 251 270 (accept_3_4 13 251 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 251 270 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 251 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 251 270 (Polychromatic418967fa.accept_13_11_4_10_1_3440 11 251 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 251 270 (accept_3_4 10 251 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 251 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 251 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 251 270
  (Polychromatic418967fa.accept_13_8_4_10_1_4358 8 251 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 251 270 (accept_3_4 7 251 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  251 270 (Polychromatic418967fa.accept_13_6_4_10_1_660 6 251 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 251 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 251 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 251 270 (accept_3_4 4 251 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 251 270 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 251 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 251 270
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 251 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 251 270 (accept_3_4 1 251 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 251
  270)))))))))))))))))))) (allB_succ' 21 250 270 (Eq.refl Bool.true) (allA_succ_of_gcd 20 250 270 10 2 25 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 250 270
  (Polychromatic418967fa.accept_13_6_3_10_1_698 19 250 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 250 270 2 9 125 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 250 270 (accept_3_5 17 250 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 250 270 2 8 125 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 250 270 5 3 50 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 250 270 2 7 125 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 250 270 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 250 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 250 270 2 6 125 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 250 270 (accept_3_5 11 250 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 250 270 10 1 25 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 250 270
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 250 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 250 270 2 4 125 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 250 270 (Polychromatic418967fa.accept_13_7_3_10_1_656 7 250 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 250 270 2 3 125 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 250 270 5 1 50 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 250 270 2 2 125 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 250 270
  (Polychromatic418967fa.accept_11_3_8_6_1_788 3 250 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 250 270 2 1 125 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 250 270 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 250 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 250 270))))))))))))))))))))) (allB_succ' 22 249 270 (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 249 270 3 7 83 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 20 249 270 (Polychromatic418967fa.accept_12_8_9_6_1_127 20 249 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 249 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 19
  249 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 249 270 3 6 83 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 249 270
  (Polychromatic418967fa.accept_19_17_2_4_1_4278 17 249 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 249 270 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 249 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 249 270 3 5 83 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 249 270 (Polychromatic418967fa.accept_12_2_9_6_1_439
  14 249 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 249 270
  (Polychromatic418967fa.accept_17_13_11_15_1_5556 13 249 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 249 270 3 4 83 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 249 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 249 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 249 270
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 249 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 249 270 3 3 83 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 249 270 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 249 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 249 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 249 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 249 270 3 2 83 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 249 270
  (Polychromatic418967fa.accept_13_5_2_10_1_248 5 249 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 249 270 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 249 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 249 270 3 1 83 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 249 270 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 249 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 249 270
  (Polychromatic418967fa.accept_11_1_7_6_1_378 1 249 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 249 270)))))))))))))))))))))) (allB_succ' 23 248 270 (Eq.refl Bool.true) (allA_succ_of_gcd 22 248 270 2 11
  124 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 248
  270 (Polychromatic418967fa.accept_12_9_8_6_1_466 21 248 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 248 270 2 10 124 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 248 270 (accept_3_4 19 248 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 248 270 2 9 124 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 248 270 (Polychromatic418967fa.accept_13_4_1_10_1_693 17 248 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 248 270 2 8 124 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 248 270
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 248 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 248 270 2 7 124 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 248 270 (accept_3_4 13 248 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 248 270 2 6 124 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 248 270 (Polychromatic418967fa.accept_13_11_1_10_1_648 11 248 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 248 270 2 5 124 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 248 270
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 248 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 248 270 2 4 124 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 248 270 (accept_3_4 7 248 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 248 270 2 3 124 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 248 270 (Polychromatic418967fa.accept_17_5_10_15_1_5574 5 248 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 248 270 2 2 124 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 248 270
  (Polychromatic418967fa.accept_12_3_8_6_1_895 3 248 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 248 270 2 1 124 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 248 270 (accept_3_4 1 248 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 248
  270))))))))))))))))))))))) (allB_succ' 24 247 270 (Eq.refl Bool.true) (allA_succ_of_accept 23 247 270 (accept_3_5 23
  247 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 247 270
  (Polychromatic418967fa.accept_26_22_13_10_1_16572 22 247 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 247 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 247 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 247 270 (accept_3_5 20 247 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 247 270 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 247 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 247 270
  (Polychromatic418967fa.accept_17_1_9_15_1_3186 18 247 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 247 270 (accept_3_5 17 247 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 247 270 (Polychromatic418967fa.accept_14_2_9_4_1_1735 16 247 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 247 270 (Polychromatic418967fa.accept_16_15_7_14_1_2883 15 247 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 247 270 (accept_3_5 14 247 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 247 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 247 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 247 270
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 247 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 247 270 (accept_3_5 11 247 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 247 270 (Polychromatic418967fa.accept_11_10_5_6_1_1842 10 247 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 247 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 247 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 247 270 (accept_3_5 8 247 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 247 270 (Polychromatic418967fa.accept_17_7_9_15_1_8105 7 247 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 247 270
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 247 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 247 270 (accept_3_5 5 247 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  247 270 (Polychromatic418967fa.accept_16_4_7_14_1_3897 4 247 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 247 270 (Polychromatic418967fa.accept_20_3_7_10_1_11035 3 247 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 247 270 (accept_3_5 2 247 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 247 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 247 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 247 270)))))))))))))))))))))))) (allB_succ' 25
  246 270 (Eq.refl Bool.true) (allA_succ_of_gcd 24 246 270 6 4 41 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 246 270 (Polychromatic418967fa.accept_17_6_8_15_1_10655 23 246
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 246 270 2 11 123 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 246 270 3 7 82 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 246 270 2 10 123 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 246 270
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 246 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 246 270 6 3 41 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 246 270 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 246 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 246 270 2 8 123 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 246 270 3 5 82 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 246 270 2 7 123 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 246 270
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 13 246 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 246 270 6 2 41 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 246 270 (Polychromatic418967fa.accept_13_11_12_10_1_2652 11 246 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 246 270 2 5 123 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 246 270 3 3 82 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 246 270 2 4 123 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 246 270
  (Polychromatic418967fa.accept_13_7_12_10_1_640 7 246 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 246 270 6 1 41 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 246 270 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 246 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 246 270 2 2 123 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 246 270 3 1 82 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 246 270 2 1 123 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 246 270
  (Polychromatic418967fa.accept_21_1_15_18_1_7646 1 246 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 246 270))))))))))))))))))))))))) (allB_succ' 26 245 270 (Eq.refl Bool.true) (allA_succ_of_gcd 25 245 270 5 5
  49 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 245 270
  (Polychromatic418967fa.accept_14_10_7_4_1_3453 24 245 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 245 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 245 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 245 270 (accept_3_4 22 245 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 245 270 (Polychromatic418967fa.accept_13_8_11_10_1_636 21 245 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 245 270 5 4 49 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 245 270 (accept_3_4 19 245 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 245 270
  (Polychromatic418967fa.accept_19_18_17_4_1_9849 18 245 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 245 270 (Polychromatic418967fa.accept_13_4_11_10_1_1226 17 245 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 245 270 (accept_3_4 16 245 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 245 270 5 3 49 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 245 270
  (Polychromatic418967fa.accept_13_1_11_10_1_1258 14 245 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 245 270 (accept_3_4 13 245 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 245 270 (Polychromatic418967fa.accept_13_12_11_10_1_2711 12 245 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 245 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 11
  245 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 245 270 5 2 49 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 245 270
  (Polychromatic418967fa.accept_11_9_3_6_1_797 9 245 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 245 270 (Polychromatic418967fa.accept_11_8_3_6_1_1855 8 245 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 245 270 (accept_3_4 7 245 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 245 270 (Polychromatic418967fa.accept_19_6_17_4_1_8491 6 245 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 245 270 5 1 49 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 245 270 (accept_3_4 4 245 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 245 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 245 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 245 270
  (Polychromatic418967fa.accept_13_2_11_10_1_1881 2 245 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 245 270 (accept_3_4 1 245 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 245
  270)))))))))))))))))))))))))) (allB_succ' 27 244 270 (Eq.refl Bool.true) (allA_succ_of_gcd 26 244 270 2 13 122 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 244 270
  (Polychromatic418967fa.accept_16_9_4_14_1_1878 25 244 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 244 270 2 12 122 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 244 270 (accept_3_5 23 244 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 244 270 2 11 122 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 244 270 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 244 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 244 270 2 10 122 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 244 270
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 244 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 244 270 2 9 122 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 244 270 (accept_3_5 17 244 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 244 270 2 8 122 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 244 270 (Polychromatic418967fa.accept_11_4_2_6_1_389 15 244 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 244 270 2 7 122 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 244 270
  (Polychromatic418967fa.accept_37_13_22_11_1_16571 13 244 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 244 270 2 6 122 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 244 270 (accept_3_5 11 244 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 244 270 2 5 122 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 244 270 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 244 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 244 270 2 4 122 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 244 270
  (Polychromatic418967fa.accept_16_7_4_14_1_2860 7 244 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 244 270 2 3 122 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 244 270 (accept_3_5 5 244 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 244 270 2 2 122 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 244 270 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 244 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 244 270 2 1 122 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 244 270
  (Polychromatic418967fa.accept_16_1_4_14_1_1896 1 244 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 244 270))))))))))))))))))))))))))) (allB_succ' 28 243 270 (Eq.refl Bool.true) (allA_succ_of_gcd 27 243 270
  27 1 9 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 243
  270 (Polychromatic418967fa.accept_12_2_3_6_1_112 26 243 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 243 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 243 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 243 270 3 8 81 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 243 270
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 243 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 243 270 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 243 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 243 270 3 7 81 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 243 270 (Polychromatic418967fa.accept_7_6_5_4_1_297 20
  243 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 243 270
  (Polychromatic418967fa.accept_13_6_9_10_1_1201 19 243 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 243 270 9 2 27 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 243 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 243 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 243 270 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 243 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 243 270 3 5 81 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 243 270
  (Polychromatic418967fa.accept_12_2_3_6_1_112 14 243 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 243 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 243 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 243 270 3 4 81 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 243 270
  (Polychromatic418967fa.accept_16_11_3_14_1_5043 11 243 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 243 270 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 243 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 243 270 9 1 27 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 243 270
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 243 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 243 270 (Polychromatic418967fa.accept_11_7_1_6_1_1281 7 243 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 243 270 3 2 81 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 243 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 243 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 243 270
  (Polychromatic418967fa.accept_12_4_3_6_1_879 4 243 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 243 270 3 1 81 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 243 270 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 243 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 243 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 243 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 243 270)))))))))))))))))))))))))))) (allB_succ'
  29 242 270 (Eq.refl Bool.true) (allA_succ_of_gcd 28 242 270 2 14 121 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 242 270 (Polychromatic418967fa.accept_12_3_2_6_1_138
  27 242 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 242 270 2 13 121 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 242 270
  (accept_3_4 25 242 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 242 270 2 12 121 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 242 270
  (Polychromatic418967fa.accept_20_3_2_10_1_3579 23 242 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 242 270 2 11 121 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 242 270 (Polychromatic418967fa.accept_12_9_2_6_1_455 21 242 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 242 270 2 10 121 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 242 270 (accept_3_4 19 242 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 242 270 2 9 121 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 242 270 (Polychromatic418967fa.accept_13_4_8_10_1_671
  17 242 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 242 270 2 8 121 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 242 270
  (Polychromatic418967fa.accept_12_3_2_6_1_138 15 242 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 242 270 2 7 121 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 242 270 (accept_3_4 13 242 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 242 270 2 6 121 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 242 270 (Polychromatic418967fa.accept_13_11_8_10_1_676 11 242 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 242 270 2 5 121 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 242 270
  (Polychromatic418967fa.accept_12_9_2_6_1_455 9 242 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 242 270 2 4 121 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 242 270 (accept_3_4 7 242 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 242 270 2 3 121 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 242 270 (Polychromatic418967fa.accept_13_5_8_10_1_4363 5 242 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 242 270 2 2 121 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 242 270
  (Polychromatic418967fa.accept_12_3_2_6_1_138 3 242 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 242 270 2 1 121 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 242 270 (accept_3_4 1 242 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 242
  270))))))))))))))))))))))))))))) (allB_succ' 30 241 270 (Eq.refl Bool.true) (allA_succ_of_accept 29 241 270
  (accept_3_5 29 241 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 241 270
  (Polychromatic418967fa.accept_19_9_13_4_1_2982 28 241 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 241 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 241 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 241 270 (accept_3_5 26 241 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 241 270 (Polychromatic418967fa.accept_13_12_7_10_1_2662 25 241 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 241 270
  (Polychromatic418967fa.accept_20_4_1_10_1_3643 24 241 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 241 270 (accept_3_5 23 241 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 241 270 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 241 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 241 270 (Polychromatic418967fa.accept_13_8_7_10_1_4362 21 241 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 241 270 (accept_3_5 20 241 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 241 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 241 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 241 270
  (Polychromatic418967fa.accept_17_1_3_15_1_2153 18 241 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 241 270 (accept_3_5 17 241 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 241 270 (Polychromatic418967fa.accept_11_5_10_6_1_793 16 241 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 241 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 241 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 241 270 (accept_3_5 14 241 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 241 270 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 241 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 241 270
  (Polychromatic418967fa.accept_13_12_7_10_1_2662 12 241 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 241 270 (accept_3_5 11 241 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 241 270 (Polychromatic418967fa.accept_19_10_13_4_1_5583 10 241 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 241 270 (Polychromatic418967fa.accept_19_9_13_4_1_2982
  9 241 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 241 270 (accept_3_5 8
  241 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 241 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 241 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 241 270 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 241 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 241 270 (accept_3_5 5 241 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 241 270 (Polychromatic418967fa.accept_13_4_7_10_1_1200 4 241 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 241 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 241 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 241 270 (accept_3_5 2 241 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  241 270 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 241 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 241 270)))))))))))))))))))))))))))))) (allB_succ' 31 240 270 (Eq.refl Bool.true)
  (allA_succ_of_gcd 30 240 270 30 1 8 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 240 270 (Polychromatic418967fa.accept_13_3_6_10_1_2658 29 240 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 240 270 2 14 120 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 240 270 3 9 80 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 240 270 2 13 120 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 240 270 5 5 48 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 240 270 6 4 40 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 240 270
  (Polychromatic418967fa.accept_14_9_2_4_1_1814 23 240 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 240 270 2 11 120 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 240 270 3 7 80 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 240 270 10 2 24 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 240 270 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 240 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 240 270 6 3 40 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 240 270
  (Polychromatic418967fa.accept_13_4_6_10_1_1199 17 240 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 240 270 2 8 120 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 240 270 15 1 16 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 14 240 270 2 7 120 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 240 270 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 240 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 240 270 6 2 40 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 240 270
  (Polychromatic418967fa.accept_19_11_12_4_1_8455 11 240 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 240 270 10 1 24 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 240 270 3 3 80 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 8 240 270 2 4 120 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 240 270 (Polychromatic418967fa.accept_17_7_2_15_1_1255 7 240 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 240 270 6 1 40 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 240 270 5 1 48 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 240 270 2 2 120 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 240 270 3 1 80 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 240 270 2 1 120 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 240 270
  (Polychromatic418967fa.accept_19_1_12_4_1_4263 1 240 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 240 270))))))))))))))))))))))))))))))) (allB_succ' 32 239 270 (Eq.refl Bool.true) (allA_succ_of_accept 31
  239 270 (accept_3_4 31 239 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 239 270
  (Polychromatic418967fa.accept_13_4_5_10_1_1247 30 239 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 239 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 239 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 239 270 (accept_3_4 28 239 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 239 270 (Polychromatic418967fa.accept_20_7_19_10_1_3567 27 239 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 239 270
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 239 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 239 270 (accept_3_4 25 239 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 239 270 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 239 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 239 270 (Polychromatic418967fa.accept_16_7_15_14_1_2889 23 239 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 239 270 (accept_3_4 22 239 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 239 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 239 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 239 270
  (Polychromatic418967fa.accept_16_4_15_14_1_5056 20 239 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 239 270 (accept_3_4 19 239 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 239 270 (Polychromatic418967fa.accept_19_18_11_4_1_7014 18 239 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 239 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 17
  239 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 239 270 (accept_3_4 16
  239 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 239 270
  (Polychromatic418967fa.accept_13_2_5_10_1_250 15 239 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 239 270 (Polychromatic418967fa.accept_11_3_8_6_1_788 14 239 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 239 270 (accept_3_4 13 239 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 239 270 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 239 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 239 270
  (Polychromatic418967fa.accept_14_11_1_4_1_4445 11 239 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 239 270 (accept_3_4 10 239 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  239 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 239 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 239 270 (Polychromatic418967fa.accept_13_8_5_10_1_2701 8 239 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 239 270 (accept_3_4 7 239 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 239 270 (Polychromatic418967fa.accept_13_6_5_10_1_1213 6 239
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 239 270
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 239 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 239 270 (accept_3_4 4 239 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  239 270 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 239 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 239 270 (Polychromatic418967fa.accept_13_2_5_10_1_250 2 239 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 239 270 (accept_3_4 1 239 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 239 270)))))))))))))))))))))))))))))))) (allB_succ' 33 238 270 (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 238 270 2 16 119 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 238 270 (Polychromatic418967fa.accept_13_5_4_10_1_1244 31 238 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 238 270 2 15 119 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 238 270 (accept_3_5 29 238 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 238 270 2 14 119 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 238 270
  (Polychromatic418967fa.accept_12_3_10_6_1_442 27 238 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 238 270 2 13 119 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 238 270 (Polychromatic418967fa.accept_19_6_10_4_1_912 25 238 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 238 270 2 12 119 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 238 270 (accept_3_5 23 238 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 238 270 2 11 119 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 238 270
  (Polychromatic418967fa.accept_12_9_10_6_1_872 21 238 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 238 270 2 10 119 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 238 270 (Polychromatic418967fa.accept_13_6_4_10_1_660 19 238 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 238 270 2 9 119 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 238 270 (accept_3_5 17 238 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 238 270 2 8 119 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 238 270
  (Polychromatic418967fa.accept_12_3_10_6_1_442 15 238 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 238 270 2 7 119 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 238 270 (Polychromatic418967fa.accept_19_13_10_4_1_4258 13 238 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 238 270 2 6 119 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 238 270 (accept_3_5 11 238 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 238 270 2 5 119 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 238 270
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 238 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 238 270 2 4 119 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 238 270 (Polychromatic418967fa.accept_13_7_4_10_1_2675 7 238 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 238 270 2 3 119 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 238 270 (accept_3_5 5 238 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 238 270 2 2 119 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 238 270 (Polychromatic418967fa.accept_12_3_10_6_1_442 3
  238 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 238 270 2 1 119 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 238 270
  (Polychromatic418967fa.accept_11_1_7_6_1_378 1 238 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 238 270))))))))))))))))))))))))))))))))) (allB_succ' 34 237 270 (Eq.refl Bool.true) (allA_succ_of_gcd 33 237
  270 3 11 79 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32
  237 270 (Polychromatic418967fa.accept_12_8_9_6_1_127 32 237 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 237 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 237 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 237 270 3 10 79 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 237 270
  (Polychromatic418967fa.accept_19_10_9_4_1_5620 29 237 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 237 270 (Polychromatic418967fa.accept_12_4_9_6_1_440 28 237 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 237 270 3 9 79 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 237 270 (Polychromatic418967fa.accept_7_5_6_4_1_117 26
  237 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 237 270
  (Polychromatic418967fa.accept_20_5_17_10_1_3632 25 237 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 237 270 3 8 79 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 237 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 237 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 237 270
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 237 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 237 270 3 7 79 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 237 270 (Polychromatic418967fa.accept_12_8_9_6_1_127 20 237 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 237 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 237 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 237 270 3 6 79 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 237 270
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 237 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 237 270 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 237 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 237 270 3 5 79 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 237 270 (Polychromatic418967fa.accept_12_2_9_6_1_439
  14 237 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 237 270
  (Polychromatic418967fa.accept_19_13_9_4_1_4309 13 237 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 237 270 3 4 79 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 237 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 237 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 237 270 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 237 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 237 270 3 3 79 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 237 270
  (Polychromatic418967fa.accept_12_8_9_6_1_127 8 237 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 237 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 237 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 237 270 3 2 79 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 237 270 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 237 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 237 270
  (Polychromatic418967fa.accept_12_4_9_6_1_440 4 237 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 237 270 3 1 79 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 237 270 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 237 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 237 270 (Polychromatic418967fa.accept_16_1_13_14_1_1064 1 237
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 237 270))))))))))))))))))))))))))))))))))
  (allB_succ' 35 236 270 (Eq.refl Bool.true) (allA_succ_of_gcd 34 236 270 2 17 118 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 236 270
  (Polychromatic418967fa.accept_12_9_8_6_1_466 33 236 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 236 270 2 16 118 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 236 270 (accept_3_4 31 236 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 236 270 2 15 118 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 236 270 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 236 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 236 270 2 14 118 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 236 270
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 236 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 236 270 2 13 118 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 236 270 (accept_3_4 25 236 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 236 270 2 12 118 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 236 270 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 236 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 236 270 2 11 118 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 236 270
  (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 236 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 236 270 2 10 118 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 236 270 (accept_3_4 19 236 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 236 270 2 9 118 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 236 270 (Polychromatic418967fa.accept_19_17_8_4_1_4212 17 236 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 236 270 2 8 118 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 236 270
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 236 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 236 270 2 7 118 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 236 270 (accept_3_4 13 236 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 236 270 2 6 118 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 236 270 (Polychromatic418967fa.accept_13_11_2_10_1_4399 11 236 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 236 270 2 5 118 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 236 270
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 236 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 236 270 2 4 118 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 236 270 (accept_3_4 7 236 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 236 270 2 3 118 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 236 270 (Polychromatic418967fa.accept_13_5_2_10_1_248 5 236 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 236 270 2 2 118 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 236 270
  (Polychromatic418967fa.accept_12_3_8_6_1_895 3 236 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 236 270 2 1 118 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 236 270 (accept_3_4 1 236 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 236
  270))))))))))))))))))))))))))))))))))) (allB_succ' 36 235 270 (Eq.refl Bool.true) (allA_succ_of_gcd 35 235 270 5 7 47
  54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 235 270
  (Polychromatic418967fa.accept_20_14_15_10_1_3554 34 235 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 235 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 235 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 235 270 (accept_3_5 32 235 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 235 270 (Polychromatic418967fa.accept_19_12_7_4_1_9873 31 235 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 235 270 5 6 47 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 235 270 (accept_3_5 29
  235 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 235 270
  (Polychromatic418967fa.accept_20_8_15_10_1_8045 28 235 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 235 270 (Polychromatic418967fa.accept_20_7_15_10_1_3628 27 235 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 235 270 (accept_3_5 26 235 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 235 270 5 5 47 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 235 270 (Polychromatic418967fa.accept_11_2_4_6_1_2412
  24 235 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 235 270 (accept_3_5 23
  235 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 235 270
  (Polychromatic418967fa.accept_13_9_1_10_1_647 22 235 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 235 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 235 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 235 270 5 4 47 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 235 270 (Polychromatic418967fa.accept_16_3_11_14_1_446
  19 235 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 235 270
  (Polychromatic418967fa.accept_20_18_15_10_1_12414 18 235 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 235 270 (accept_3_5 17 235 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 235 270 (Polychromatic418967fa.accept_17_16_14_15_1_1250 16 235 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 235 270 5 3 47 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 235 270 (accept_3_5 14 235 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 235 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 235 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 235 270
  (Polychromatic418967fa.accept_17_12_14_15_1_5561 12 235 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 235 270 (accept_3_5 11 235 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 235 270 5 2 47 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 235 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 235 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 235 270 (accept_3_5 8 235 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 235 270 (Polychromatic418967fa.accept_14_7_11_4_1_3455 7 235 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 235 270
  (Polychromatic418967fa.accept_17_6_14_15_1_5505 6 235 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 235 270 5 1 47 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 235 270 (Polychromatic418967fa.accept_13_4_1_10_1_693 4 235 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 235 270 (Polychromatic418967fa.accept_16_3_11_14_1_446 3 235
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 235 270 (accept_3_5 2 235 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 235 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 1
  235 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 235
  270)))))))))))))))))))))))))))))))))))) (allB_succ' 37 234 270 (Eq.refl Bool.true) (allA_succ_of_gcd 36 234 270 18 2
  13 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 234 270
  (Polychromatic418967fa.accept_14_7_10_4_1_130 35 234 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 234 270 2 17 117 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 234 270 3 11 78 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 234 270 2 16 117 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 234 270 (Polychromatic418967fa.accept_11_9_3_6_1_797 31 234 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 234 270 6 5 39 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 234 270
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 234 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 234 270 2 14 117 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 27 234 270 9 3 26 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 234 270 2 13 117 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 234 270 (Polychromatic418967fa.accept_17_8_13_15_1_2143 25 234 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 234 270 6 4 39 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 234 270
  (Polychromatic418967fa.accept_16_7_10_14_1_1884 23 234 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 234 270 2 11 117 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 21 234 270 3 7 78 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 20 234 270 2 10 117 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 234 270 (Polychromatic418967fa.accept_11_8_3_6_1_1855 19 234
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 234 270 18 1 13 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 234 270
  (Polychromatic418967fa.accept_19_17_6_4_1_7027 17 234 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 234 270 2 8 117 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 234 270 3 5 78 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 234 270 2 7 117 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 234 270 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 234 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 234 270 6 2 39 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 234 270
  (Polychromatic418967fa.accept_17_11_13_15_1_2140 11 234 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 234 270 2 5 117 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 234 270 9 1 26 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 8 234 270 2 4 117 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 234 270 (Polychromatic418967fa.accept_14_7_10_4_1_130 7 234 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 234 270 6 1 39 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 234 270
  (Polychromatic418967fa.accept_16_5_10_14_1_5074 5 234 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 234 270 2 2 117 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 3 234 270 3 1 78 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 2 234 270 2 1 117 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 234 270 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 234 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 234 270))))))))))))))))))))))))))))))))))))) (allB_succ'
  38 233 270 (Eq.refl Bool.true) (allA_succ_of_accept 37 233 270 (accept_3_4 37 233 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 233 270 (Polychromatic418967fa.accept_16_4_9_14_1_3883 36 233 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 233 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 233 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 233 270 (accept_3_4 34 233 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 233 270 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 233 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 233 270 (Polychromatic418967fa.accept_13_6_12_10_1_690 32 233 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 233 270 (accept_3_4 31 233 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 233 270 (Polychromatic418967fa.accept_14_2_9_4_1_1735 30 233
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 233 270
  (Polychromatic418967fa.accept_20_9_13_10_1_452 29 233 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 233 270 (accept_3_4 28 233 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 233 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 233 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 233 270 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 233 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 233 270 (accept_3_4 25 233 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 233 270 (Polychromatic418967fa.accept_13_11_12_10_1_2652 24 233 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 233 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 233 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 233 270 (accept_3_4 22 233 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 233 270 (Polychromatic418967fa.accept_13_8_12_10_1_4414 21 233 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 233 270 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 233 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 233 270 (accept_3_4 19 233 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 233 270 (Polychromatic418967fa.accept_17_1_12_15_1_1263 18 233 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 233 270
  (Polychromatic418967fa.accept_20_17_13_10_1_5059 17 233 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 233 270 (accept_3_4 16 233 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 233 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 233 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 233 270 (Polychromatic418967fa.accept_17_14_12_15_1_5558 14
  233 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 233 270 (accept_3_4 13
  233 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 233 270
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 233 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 233 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 233 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 233 270 (accept_3_4 10 233 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 233 270 (Polychromatic418967fa.accept_13_9_12_10_1_242 9 233 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 233 270
  (Polychromatic418967fa.accept_13_8_12_10_1_4414 8 233 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 233 270 (accept_3_4 7 233 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  233 270 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 233 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 233 270 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 233 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 233 270 (accept_3_4 4 233 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 233 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 233 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 233 270
  (Polychromatic418967fa.accept_13_2_12_10_1_2649 2 233 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 233 270 (accept_3_4 1 233 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 233
  270)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 232 270 (Eq.refl Bool.true) (allA_succ_of_gcd 38 232 270 2 19
  116 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 232
  270 (Polychromatic418967fa.accept_22_15_12_6_1_8744 37 232 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 232 270 2 18 116 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 232 270 (accept_3_5 35 232 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 232 270 2 17 116 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 232 270 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 232 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 232 270 2 16 116 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 232 270
  (Polychromatic418967fa.accept_7_3_1_4_1_121 31 232 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 232 270 2 15 116 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 232 270 (accept_3_5 29 232 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 232 270 2 14 116 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 232 270 (Polychromatic418967fa.accept_11_5_1_6_1_774 27 232 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 232 270 2 13 116 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 232 270
  (Polychromatic418967fa.accept_13_12_11_10_1_2711 25 232 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 232 270 2 12 116 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 232 270 (accept_3_5 23 232 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 232 270 2 11 116 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 232 270 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 232 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 232 270 2 10 116 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 232 270
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 232 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 232 270 2 9 116 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 232 270 (accept_3_5 17 232 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 232 270 2 8 116 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 232 270 (Polychromatic418967fa.accept_12_3_4_6_1_434 15 232 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 232 270 2 7 116 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 232 270
  (Polychromatic418967fa.accept_17_13_11_15_1_5556 13 232 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 232 270 2 6 116 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 232 270 (accept_3_5 11 232 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 232 270 2 5 116 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 232 270 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 232 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 232 270 2 4 116 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 232 270
  (Polychromatic418967fa.accept_11_7_1_6_1_1281 7 232 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 232 270 2 3 116 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 232 270 (accept_3_5 5 232 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 232 270 2 2 116 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 232 270 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 232 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 232 270 2 1 116 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 232 270
  (Polychromatic418967fa.accept_13_1_11_10_1_1258 1 232 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 232 270))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 231 270 (Eq.refl Bool.true) (allA_succ_of_gcd
  39 231 270 3 13 77 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 231 270 (Polychromatic418967fa.accept_12_2_3_6_1_112 38 231 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 231 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 231 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 231 270 3 12 77 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 231 270
  (Polychromatic418967fa.accept_19_16_3_4_1_4281 35 231 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 231 270 (Polychromatic418967fa.accept_12_10_3_6_1_882 34 231 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 231 270 3 11 77 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 231 270 (Polychromatic418967fa.accept_12_8_3_6_1_909
  32 231 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 231 270
  (Polychromatic418967fa.accept_14_3_7_4_1_118 31 231 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 231 270 3 10 77 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 231 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 231 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 231 270 (Polychromatic418967fa.accept_12_4_3_6_1_879
  28 231 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 231 270 3 9 77 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 231 270
  (Polychromatic418967fa.accept_12_2_3_6_1_112 26 231 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 231 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 231 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 231 270 3 8 77 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 231 270
  (Polychromatic418967fa.accept_20_3_11_10_1_3545 23 231 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 231 270 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 231 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 231 270 3 7 77 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 231 270
  (Polychromatic418967fa.accept_12_8_3_6_1_909 20 231 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 231 270 (Polychromatic418967fa.accept_17_2_10_15_1_1238 19 231 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 231 270 3 6 77 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 231 270
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 231 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 231 270 (Polychromatic418967fa.accept_12_4_3_6_1_879 16 231 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 231 270 3 5 77 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 231 270 (Polychromatic418967fa.accept_12_2_3_6_1_112
  14 231 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 231 270
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 231 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 231 270 3 4 77 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 231 270 (Polychromatic418967fa.accept_14_11_7_4_1_3449 11 231 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 231 270 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 231
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 231 270 3 3 77 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 231 270
  (Polychromatic418967fa.accept_12_8_3_6_1_909 8 231 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 231 270 (Polychromatic418967fa.accept_19_7_3_4_1_13881 7 231 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 231 270 3 2 77 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 231 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 231 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 231 270
  (Polychromatic418967fa.accept_12_4_3_6_1_879 4 231 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 231 270 3 1 77 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 231 270 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 231 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 231 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 231 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 231 270))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 41 230 270 (Eq.refl Bool.true) (allA_succ_of_gcd 40 230 270 10 4 23 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 230 270
  (Polychromatic418967fa.accept_12_3_2_6_1_138 39 230 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 230 270 2 19 115 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 230 270 (accept_3_4 37 230 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 230 270 2 18 115 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 35 230 270 5 7 46 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 34 230 270 2 17 115 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 230 270 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 230 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 230 270 2 16 115 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 230 270 (accept_3_4 31 230 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 230 270 10 3 23 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 230 270
  (Polychromatic418967fa.accept_24_5_14_6_1_6131 29 230 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 230 270 2 14 115 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 230 270 (Polychromatic418967fa.accept_11_5_10_6_1_793 27 230 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 230 270 2 13 115 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 230 270 5 5 46 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 230 270 2 12 115 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 230 270
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 230 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 230 270 2 11 115 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 230 270 (Polychromatic418967fa.accept_12_9_2_6_1_455 21 230 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 230 270 10 2 23 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 230 270 (accept_3_4 19 230 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 230 270 2 9 115 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 230 270 (Polychromatic418967fa.accept_7_3_6_4_1_30 17
  230 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 230 270 2 8 115 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 230 270 5 3 46 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 230 270 2 7 115 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 230 270
  (accept_3_4 13 230 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 230 270 2 6 115 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 230 270
  (Polychromatic418967fa.accept_19_11_2_4_1_8443 11 230 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 230 270 10 1 23 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 230 270 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 230 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 230 270 2 4 115 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 230 270 (accept_3_4 7 230 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 230 270 2 3 115 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 230 270 5 1 46 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 230 270 2 2 115 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 230 270
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 230 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 230 270 2 1 115 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 230 270 (accept_3_4 1 230 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 230
  270))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 229 270 (Eq.refl Bool.true) (allA_succ_of_accept 41 229
  270 (accept_3_5 41 229 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 229 270
  (Polychromatic418967fa.accept_17_6_8_15_1_10655 40 229 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 229 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 229 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 229 270 (accept_3_5 38 229 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 229 270 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 229 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 229 270
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 229 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 229 270 (accept_3_5 35 229 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 229 270 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 229 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 229 270 (Polychromatic418967fa.accept_13_7_8_10_1_2663 33 229 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 229 270 (accept_3_5 32 229 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 229 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 229 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 229 270
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 229 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 229 270 (accept_3_5 29 229 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 229 270 (Polychromatic418967fa.accept_13_2_8_10_1_1902 28 229 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 229 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 229 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 229 270 (accept_3_5 26 229 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 229 270 (Polychromatic418967fa.accept_11_3_9_6_1_105 25 229 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 229 270
  (Polychromatic418967fa.accept_13_11_8_10_1_676 24 229 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 229 270 (accept_3_5 23 229 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 229 270 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 229 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 229 270 (Polychromatic418967fa.accept_20_1_9_10_1_6491 21 229 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 229 270 (accept_3_5 20 229 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 229 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 229 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 229 270
  (Polychromatic418967fa.accept_13_5_8_10_1_4363 18 229 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 229 270 (accept_3_5 17 229 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 229 270 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 229 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 229 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 229 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 229 270 (accept_3_5 14 229 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 229 270 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 229 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 229 270
  (Polychromatic418967fa.accept_13_12_8_10_1_1879 12 229 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 229 270 (accept_3_5 11 229 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 229 270 (Polychromatic418967fa.accept_16_10_5_14_1_6173 10 229 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 229 270 (Polychromatic418967fa.accept_7_2_5_4_1_115 9
  229 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 229 270 (accept_3_5 8 229
  270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 229 270 (Polychromatic418967fa.accept_4_3_1_2_1_62
  7 229 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 229 270
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 229 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 229 270 (accept_3_5 5 229 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  229 270 (Polychromatic418967fa.accept_13_4_8_10_1_671 4 229 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 229 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 229 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 229 270 (accept_3_5 2 229 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 229 270 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 229 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 229 270))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 43 228 270 (Eq.refl Bool.true) (allA_succ_of_gcd 42 228 270 6 7 38 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 228 270
  (Polychromatic418967fa.accept_16_9_4_14_1_1878 41 228 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 228 270 2 20 114 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 228 270 3 13 76 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 228 270 2 19 114 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 228 270 (Polychromatic418967fa.accept_20_17_8_10_1_8081 37 228
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 228 270 6 6 38 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 228 270
  (Polychromatic418967fa.accept_20_15_8_10_1_3602 35 228 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 228 270 2 17 114 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 33 228 270 3 11 76 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 228 270 2 16 114 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 228 270
  (Polychromatic418967fa.accept_16_15_4_14_1_6123 31 228 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 228 270 6 5 38 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 228 270 (Polychromatic418967fa.accept_13_3_7_10_1_668 29 228 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 228 270 2 14 114 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 228 270 3 9 76 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 228 270 2 13 114 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 228 270
  (Polychromatic418967fa.accept_11_3_8_6_1_788 25 228 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 228 270 6 4 38 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 228 270 (Polychromatic418967fa.accept_16_7_4_14_1_2860 23 228 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 228 270 2 11 114 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 228 270 3 7 76 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 228 270 2 10 114 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 228 270
  (Polychromatic418967fa.accept_17_2_7_15_1_5525 19 228 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 228 270 6 3 38 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 228 270 (Polychromatic418967fa.accept_13_4_7_10_1_1200 17 228 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 228 270 2 8 114 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 228 270 3 5 76 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 228 270 2 7 114 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 228 270
  (Polychromatic418967fa.accept_24_13_12_6_1_16570 13 228 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 228 270 6 2 38 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 228 270 (Polychromatic418967fa.accept_23_11_21_17_1_6682 11 228 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 228 270 2 5 114 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 228 270 3 3 76 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 228 270 2 4 114 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 228 270
  (Polychromatic418967fa.accept_16_7_4_14_1_2860 7 228 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 228 270 6 1 38 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 228 270 (Polychromatic418967fa.accept_17_5_7_15_1_1230 5 228 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 228 270 2 2 114 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 228 270 3 1 76 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 228 270 2 1 114 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 228 270
  (Polychromatic418967fa.accept_16_1_4_14_1_1896 1 228 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 228 270))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 227 270 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 227 270 (accept_3_4 43 227 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 227 270 (Polychromatic418967fa.accept_13_3_6_10_1_2658 42 227 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 227 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 227 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 227 270 (accept_3_4 40 227 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 227 270 (Polychromatic418967fa.accept_20_19_7_10_1_12343 39 227 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 227 270
  (Polychromatic418967fa.accept_13_12_6_10_1_667 38 227 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 227 270 (accept_3_4 37 227 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 227 270 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 227 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 227 270 (Polychromatic418967fa.accept_13_9_6_10_1_666 35 227 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 227 270 (accept_3_4 34 227 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 227 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 227 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 227 270
  (Polychromatic418967fa.accept_25_7_2_20_1_16569 32 227 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 227 270 (accept_3_4 31 227 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 227 270 (Polychromatic418967fa.accept_13_4_6_10_1_1199 30 227 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 227 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 227 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 227 270 (accept_3_4 28 227 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 227 270 (Polychromatic418967fa.accept_7_6_3_4_1_294
  27 227 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 227 270
  (Polychromatic418967fa.accept_17_9_6_15_1_5454 26 227 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 227 270 (accept_3_4 25 227 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 227 270 (Polychromatic418967fa.accept_19_5_18_4_1_2956 24 227 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 227 270 (Polychromatic418967fa.accept_11_1_7_6_1_378 23 227 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 227 270 (accept_3_4 22 227 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 227 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 227 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 227 270
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 227 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 227 270 (accept_3_4 19 227 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 227 270 (Polychromatic418967fa.accept_13_5_6_10_1_2659 18 227 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 227 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 227 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 227 270 (accept_3_4 16 227 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 227 270 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 227 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 227 270
  (Polychromatic418967fa.accept_17_14_6_15_1_3151 14 227 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 227 270 (accept_3_4 13 227 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 227 270 (Polychromatic418967fa.accept_11_1_7_6_1_378 12 227 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 227 270 (Polychromatic418967fa.accept_16_11_3_14_1_5043 11 227
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 227 270 (accept_3_4 10 227
  270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 227 270 (Polychromatic418967fa.accept_4_1_3_2_1_3
  9 227 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 227 270
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 227 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 227 270 (accept_3_4 7 227 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  227 270 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 227 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 227 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 227 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 227 270 (accept_3_4 4 227 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 227 270 (Polychromatic418967fa.accept_13_3_6_10_1_2658 3 227 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 227 270
  (Polychromatic418967fa.accept_13_2_6_10_1_2703 2 227 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 227 270 (accept_3_4 1 227 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 227
  270)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 226 270 (Eq.refl Bool.true) (allA_succ_of_gcd 44 226
  270 2 22 113 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  43 226 270 (Polychromatic418967fa.accept_13_4_5_10_1_1247 43 226 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 226 270 2 21 113 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 226 270 (accept_3_5 41 226 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 226 270 2 20 113 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 226 270 (Polychromatic418967fa.accept_12_3_10_6_1_442 39 226 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 226 270 2 19 113 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 226 270
  (Polychromatic418967fa.accept_14_9_2_4_1_1814 37 226 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 226 270 2 18 113 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 226 270 (accept_3_5 35 226 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 226 270 2 17 113 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 226 270 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 226 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 226 270 2 16 113 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 226 270
  (Polychromatic418967fa.accept_25_6_1_20_1_16568 31 226 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 226 270 2 15 113 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 226 270 (accept_3_5 29 226 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 226 270 2 14 113 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 226 270 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 226 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 226 270 2 13 113 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 226 270
  (Polychromatic418967fa.accept_19_6_17_4_1_8491 25 226 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 226 270 2 12 113 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 226 270 (accept_3_5 23 226 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 226 270 2 11 113 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 226 270 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 226 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 226 270 2 10 113 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 226 270
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 226 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 226 270 2 9 113 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 226 270 (accept_3_5 17 226 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 226 270 2 8 113 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 226 270 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 226 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 226 270 2 7 113 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 226 270
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 226 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 226 270 2 6 113 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 226 270 (accept_3_5 11 226 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 226 270 2 5 113 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 226 270 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 226 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 226 270 2 4 113 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 226 270
  (Polychromatic418967fa.accept_17_7_5_15_1_3184 7 226 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 226 270 2 3 113 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 226 270 (accept_3_5 5 226 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 226 270 2 2 113 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 226 270 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 226 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 226 270 2 1 113 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 226 270
  (Polychromatic418967fa.accept_19_1_17_4_1_8520 1 226 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 226 270))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 225 270 (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 225 270 45 1 5 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 225 270 (Polychromatic418967fa.accept_12_8_9_6_1_127 44 225 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 225 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 225 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 225 270 3 14 75 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 225 270
  (Polychromatic418967fa.accept_19_3_16_4_1_7076 41 225 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 225 270 5 8 45 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 225 270 3 13 75 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 225 270 (Polychromatic418967fa.accept_7_3_1_4_1_121 38 225 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 225 270
  (Polychromatic418967fa.accept_13_11_4_10_1_3440 37 225 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 225 270 9 4 25 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 35 225 270 5 7 45 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 225 270 (Polychromatic418967fa.accept_11_1_5_6_1_397 34 225 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 225 270 3 11 75 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 225 270
  (Polychromatic418967fa.accept_11_10_5_6_1_1842 32 225 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 225 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 225 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 225 270 15 2 15 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 225 270
  (Polychromatic418967fa.accept_16_13_1_14_1_2855 29 225 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 225 270 (Polychromatic418967fa.accept_12_4_9_6_1_440 28 225 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 225 270 9 3 25 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 225 270
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 225 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 225 270 5 5 45 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 225 270 3 8 75 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 225 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 225 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 225 270 (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 225
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 225 270 3 7 75 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 225 270 5 4 45 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 225 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 225 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 225 270 9 2 25 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 225 270 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 225 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 225 270 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 225
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 225 270 15 1 15 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 225 270
  (Polychromatic418967fa.accept_12_2_9_6_1_439 14 225 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 225 270 (Polychromatic418967fa.accept_16_13_1_14_1_2855 13 225 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 225 270 3 4 75 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 225 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 225 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 225 270 5 2 45 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 225 270 9 1 25 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 225 270 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 225 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 225 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 225 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 225 270 3 2 75 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 225 270 5 1 45 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 225 270
  (Polychromatic418967fa.accept_12_4_9_6_1_440 4 225 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 225 270 3 1 75 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 225 270 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 225 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 225 270 (Polychromatic418967fa.accept_11_1_5_6_1_397 1 225 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 225
  270)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 224 270 (Eq.refl Bool.true) (allA_succ_of_gcd 46 224
  270 2 23 112 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  45 224 270 (Polychromatic418967fa.accept_12_9_8_6_1_466 45 224 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 224 270 2 22 112 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 224 270 (accept_3_4 43 224 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 224 270 2 21 112 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 224 270 (Polychromatic418967fa.accept_13_2_3_10_1_658 41 224 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 224 270 2 20 112 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 224 270
  (Polychromatic418967fa.accept_12_3_8_6_1_895 39 224 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 224 270 2 19 112 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 224 270 (accept_3_4 37 224 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 224 270 2 18 112 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 224 270 (Polychromatic418967fa.accept_11_2_4_6_1_2412 35 224 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 224 270 2 17 112 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 224 270
  (Polychromatic418967fa.accept_12_9_8_6_1_466 33 224 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 224 270 2 16 112 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 224 270 (accept_3_4 31 224 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 224 270 2 15 112 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 224 270 (Polychromatic418967fa.accept_17_12_3_15_1_5476 29 224 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 224 270 2 14 112 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 224 270
  (Polychromatic418967fa.accept_12_3_8_6_1_895 27 224 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 224 270 2 13 112 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 224 270 (accept_3_4 25 224 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 224 270 2 12 112 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 224 270 (Polychromatic418967fa.accept_31_23_7_22_1_16567 23 224 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 224 270 2 11 112 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 224 270
  (Polychromatic418967fa.accept_12_9_8_6_1_466 21 224 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 224 270 2 10 112 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 224 270 (accept_3_4 19 224 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 224 270 2 9 112 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 224 270 (Polychromatic418967fa.accept_21_17_14_18_1_13621 17 224 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 224 270 2 8 112 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 224 270
  (Polychromatic418967fa.accept_12_3_8_6_1_895 15 224 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 224 270 2 7 112 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 224 270 (accept_3_4 13 224 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 224 270 2 6 112 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 224 270 (Polychromatic418967fa.accept_13_11_3_10_1_4374 11 224 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 224 270 2 5 112 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 224 270
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 224 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 224 270 2 4 112 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 224 270 (accept_3_4 7 224 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 224 270 2 3 112 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 224 270 (Polychromatic418967fa.accept_19_5_15_4_1_4224 5 224 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 224 270 2 2 112 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 224 270
  (Polychromatic418967fa.accept_12_3_8_6_1_895 3 224 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 224 270 2 1 112 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 224 270 (accept_3_4 1 224 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 224
  270))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 223 270 (Eq.refl Bool.true) (allA_succ_of_accept 47
  223 270 (accept_3_5 47 223 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 223 270
  (Polychromatic418967fa.accept_19_8_14_4_1_2967 46 223 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 223 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 223 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 223 270 (accept_3_5 44 223 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 223 270 (Polychromatic418967fa.accept_22_21_3_6_1_8825 43 223 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 223 270
  (Polychromatic418967fa.accept_11_9_3_6_1_797 42 223 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 223 270 (accept_3_5 41 223 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 223 270 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 223 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 223 270 (Polychromatic418967fa.accept_16_7_15_14_1_2889 39 223 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 223 270 (accept_3_5 38 223 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 223 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 223 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 223 270
  (Polychromatic418967fa.accept_16_4_15_14_1_5056 36 223 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 223 270 (accept_3_5 35 223 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 223 270 (Polychromatic418967fa.accept_13_8_2_10_1_652 34 223 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 223 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 223 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 223 270 (accept_3_5 32 223 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 223 270 (Polychromatic418967fa.accept_7_3_6_4_1_30 31
  223 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 223 270
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 223 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 223 270 (accept_3_5 29 223 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 223 270 (Polychromatic418967fa.accept_19_9_14_4_1_5595 28 223 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 223 270 (Polychromatic418967fa.accept_17_10_2_15_1_3179 27 223 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 223 270 (accept_3_5 26 223 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 223 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 223 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 223 270
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 223 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 223 270 (accept_3_5 23 223 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 223 270 (Polychromatic418967fa.accept_20_2_3_10_1_5075 22 223 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 223 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 223 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 223 270 (accept_3_5 20 223 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 223 270 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 223 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 223 270
  (Polychromatic418967fa.accept_13_5_2_10_1_248 18 223 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 223 270 (accept_3_5 17 223 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 223 270 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 223 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 223 270 (Polychromatic418967fa.accept_19_15_14_4_1_4267 15 223 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 223 270 (accept_3_5 14 223 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 223 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 223 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 223 270
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 223 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 223 270 (accept_3_5 11 223 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 223 270 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 223 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 223 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 223 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 223 270 (accept_3_5 8 223 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 223 270 (Polychromatic418967fa.accept_16_7_15_14_1_2889 7 223 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 223 270
  (Polychromatic418967fa.accept_13_6_2_10_1_1240 6 223 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 223 270 (accept_3_5 5 223 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  223 270 (Polychromatic418967fa.accept_16_4_15_14_1_5056 4 223 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 223 270 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 223 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 223 270 (accept_3_5 2 223 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 223 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 223 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 223 270))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 49 222 270 (Eq.refl Bool.true) (allA_succ_of_gcd 48 222 270 6 8 37 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 222 270
  (Polychromatic418967fa.accept_19_9_13_4_1_2982 47 222 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 222 270 2 23 111 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 222 270 3 15 74 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 222 270 2 22 111 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 222 270 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 222 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 222 270 6 7 37 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 222 270
  (Polychromatic418967fa.accept_7_6_5_4_1_297 41 222 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 222 270 2 20 111 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 222 270 3 13 74 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 222 270 2 19 111 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 222 270 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 222 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 222 270 6 6 37 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 222 270
  (Polychromatic418967fa.accept_13_9_1_10_1_647 35 222 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 222 270 2 17 111 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 222 270 3 11 74 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 222 270 2 16 111 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 222 270 (Polychromatic418967fa.accept_23_8_15_17_1_14864 31 222
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 222 270 6 5 37 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 222 270
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 222 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 222 270 2 14 111 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 27 222 270 3 9 74 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 222 270 2 13 111 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 222 270 (Polychromatic418967fa.accept_19_6_13_4_1_876 25 222 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 222 270 6 4 37 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 222 270
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 222 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 222 270 2 11 111 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 222 270 3 7 74 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 222 270 2 10 111 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 222 270 (Polychromatic418967fa.accept_21_19_12_18_1_1798 19 222 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 222 270 6 3 37 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 222 270
  (Polychromatic418967fa.accept_13_4_1_10_1_693 17 222 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 222 270 2 8 111 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 222 270 3 5 74 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 222 270 2 7 111 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 222 270 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 222 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 222 270 6 2 37 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 222 270
  (Polychromatic418967fa.accept_13_11_1_10_1_648 11 222 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 222 270 2 5 111 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 222 270 3 3 74 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 222 270 2 4 111 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 7 222 270 (Polychromatic418967fa.accept_19_7_13_4_1_1824 7 222 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 222 270 6 1 37 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 222 270
  (Polychromatic418967fa.accept_20_5_2_10_1_3576 5 222 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 222 270 2 2 111 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 3 222 270 3 1 74 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 2 222 270 2 1 111 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 222 270 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 222 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 222 270)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 50 221 270 (Eq.refl Bool.true) (allA_succ_of_accept 49 221 270 (accept_3_4 49 221 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 221 270 (Polychromatic418967fa.accept_21_6_11_18_1_10664 48 221 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 221 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 221 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 221 270 (accept_3_4 46 221 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 221 270 (Polychromatic418967fa.accept_19_7_12_4_1_8522 45 221 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 221 270 (Polychromatic418967fa.accept_19_6_12_4_1_8516 44 221 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 221 270 (accept_3_4 43 221 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 221 270 (Polychromatic418967fa.accept_16_10_13_14_1_5042 42
  221 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 221 270
  (Polychromatic418967fa.accept_21_20_11_18_1_3037 41 221 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 221 270 (accept_3_4 40 221 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 221 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 221 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 221 270 (Polychromatic418967fa.accept_11_5_1_6_1_774 38 221
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 221 270 (accept_3_4 37 221
  270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 221 270
  (Polychromatic418967fa.accept_14_8_11_4_1_3438 36 221 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 221 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 221 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 221 270 (accept_3_4 34 221 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 221 270 (Polychromatic418967fa.accept_16_1_13_14_1_1064 33 221 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 221 270
  (Polychromatic418967fa.accept_23_9_14_17_1_16566 32 221 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 221 270 (accept_3_4 31 221 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 221 270 (Polychromatic418967fa.accept_19_11_12_4_1_8455 30 221 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 221 270 (Polychromatic418967fa.accept_11_7_1_6_1_1281
  29 221 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 221 270 (accept_3_4 28
  221 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 221 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 221 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 221 270 (Polychromatic418967fa.accept_16_10_13_14_1_5042 26 221 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 221 270 (accept_3_4 25 221 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 221 270 (Polychromatic418967fa.accept_19_5_12_4_1_8467 24 221 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 221 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 221 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 221 270 (accept_3_4 22 221 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 221 270 (Polychromatic418967fa.accept_14_7_11_4_1_3455 21 221 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 221 270 (Polychromatic418967fa.accept_19_1_12_4_1_4263 20 221 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 221 270 (accept_3_4 19 221 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 221 270 (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 221
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 221 270
  (Polychromatic418967fa.accept_16_1_13_14_1_1064 17 221 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 221 270 (accept_3_4 16 221 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 221 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 221 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 221 270 (Polychromatic418967fa.accept_20_14_1_10_1_12401 14
  221 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 221 270 (accept_3_4 13
  221 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 221 270
  (Polychromatic418967fa.accept_21_12_11_18_1_7570 12 221 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 221 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 221 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 221 270 (accept_3_4 10 221 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 221 270 (Polychromatic418967fa.accept_20_9_1_10_1_6466 9 221 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 221 270
  (Polychromatic418967fa.accept_14_8_11_4_1_3438 8 221 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 221 270 (accept_3_4 7 221 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  221 270 (Polychromatic418967fa.accept_19_6_12_4_1_8516 6 221 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 221 270 (Polychromatic418967fa.accept_11_5_1_6_1_774 5 221 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 221 270 (accept_3_4 4 221 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 221 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 221 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 221 270
  (Polychromatic418967fa.accept_19_2_12_4_1_4193 2 221 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 221 270 (accept_3_4 1 221 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 221
  270)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 220 270 (Eq.refl Bool.true) (allA_succ_of_gcd 50
  220 270 10 5 22 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 220 270 (Polychromatic418967fa.accept_14_7_10_4_1_130 49 220 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 220 270 2 24 110 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 220 270 (accept_3_5 47 220 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 220 270 2 23 110 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 220 270 5 9 44 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 220 270 2 22 110 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 220 270 (Polychromatic418967fa.accept_7_1_3_4_1_128 43
  220 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 220 270 2 21 110 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 220 270
  (accept_3_5 41 220 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 220 270 10 4 22 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 220 270
  (Polychromatic418967fa.accept_12_3_4_6_1_434 39 220 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 220 270 2 19 110 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 220 270 (Polychromatic418967fa.accept_13_11_12_10_1_2652 37 220 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 220 270 2 18 110 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 220 270 5 7 44 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 220 270 2 17 110 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 220 270
  (Polychromatic418967fa.accept_12_9_4_6_1_460 33 220 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 220 270 2 16 110 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 220 270 (Polychromatic418967fa.accept_17_14_16_15_1_5509 31 220 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 220 270 10 3 22 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 220 270 (accept_3_5 29 220 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 220 270 2 14 110 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 220 270
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 220 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 220 270 2 13 110 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 25 220 270 5 5 44 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 220 270 2 12 110 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 220 270 (accept_3_5 23 220 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 220 270 2 11 110 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 220 270 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 220 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 220 270 10 2 22 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 220 270
  (Polychromatic418967fa.accept_13_6_12_10_1_690 19 220 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 220 270 2 9 110 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 220 270 (accept_3_5 17 220 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 220 270 2 8 110 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 220 270 5 3 44 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 220 270 2 7 110 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 220 270 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 220 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 220 270 2 6 110 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 220 270 (accept_3_5 11 220 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 220 270 10 1 22 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 220 270
  (Polychromatic418967fa.accept_12_9_4_6_1_460 9 220 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 220 270 2 4 110 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 220 270 (Polychromatic418967fa.accept_13_7_12_10_1_640 7 220 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 220 270 2 3 110 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 220 270 5 1 44 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 220 270 2 2 110 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 220 270
  (Polychromatic418967fa.accept_12_3_4_6_1_434 3 220 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 220 270 2 1 110 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 220 270 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 220 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 220 270)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 52 219 270 (Eq.refl Bool.true) (allA_succ_of_gcd 51 219 270 3 17 73 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 219 270
  (Polychromatic418967fa.accept_12_2_3_6_1_112 50 219 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 219 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 219 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 219 270 3 16 73 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 219 270 (Polychromatic418967fa.accept_7_5_2_4_1_126 47
  219 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 219 270
  (Polychromatic418967fa.accept_12_10_3_6_1_882 46 219 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 219 270 3 15 73 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 219 270 (Polychromatic418967fa.accept_12_8_3_6_1_909 44 219 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 219 270
  (Polychromatic418967fa.accept_13_4_11_10_1_1226 43 219 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 219 270 3 14 73 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 219 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 219 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 219 270
  (Polychromatic418967fa.accept_7_5_2_4_1_126 40 219 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 219 270 3 13 73 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 219 270 (Polychromatic418967fa.accept_11_5_10_6_1_793 38 219 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 219 270
  (Polychromatic418967fa.accept_4_1_3_2_1_3 37 219 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 219 270 3 12 73 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 219 270 (Polychromatic418967fa.accept_16_3_11_14_1_446 35 219 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 219 270
  (Polychromatic418967fa.accept_7_6_2_4_1_291 34 219 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 219 270 3 11 73 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 219 270 (Polychromatic418967fa.accept_12_8_3_6_1_909 32 219 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 219 270
  (Polychromatic418967fa.accept_20_11_19_10_1_3568 31 219 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 219 270 3 10 73 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 219 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 219 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 219 270
  (Polychromatic418967fa.accept_12_4_3_6_1_879 28 219 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 219 270 3 9 73 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 219 270 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 219 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 219 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 219 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 219 270 3 8 73 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 219 270
  (Polychromatic418967fa.accept_20_3_19_10_1_12337 23 219 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 219 270 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 219 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 219 270 3 7 73 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 219 270
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 219 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 219 270 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 219 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 219 270 3 6 73 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 219 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 17
  219 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 219 270
  (Polychromatic418967fa.accept_11_5_10_6_1_793 16 219 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 219 270 3 5 73 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 219 270 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 219 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 219 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 219 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 219 270 3 4 73 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 219 270
  (Polychromatic418967fa.accept_20_11_19_10_1_3568 11 219 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 219 270 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 219 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 219 270 3 3 73 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 219 270
  (Polychromatic418967fa.accept_12_8_3_6_1_909 8 219 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 219 270 (Polychromatic418967fa.accept_20_7_19_10_1_3567 7 219 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 219 270 3 2 73 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 219 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 219 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 219 270
  (Polychromatic418967fa.accept_12_4_3_6_1_879 4 219 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 219 270 3 1 73 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 219 270 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 219 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 219 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 219 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 219
  270)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 218 270 (Eq.refl Bool.true) (allA_succ_of_gcd
  52 218 270 2 26 109 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 218 270 (Polychromatic418967fa.accept_12_3_2_6_1_138 51 218 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 218 270 2 25 109 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 218 270 (accept_3_4 49 218 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 218 270 2 24 109 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 218 270 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 218 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 218 270 2 23 109 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 218 270
  (Polychromatic418967fa.accept_7_3_1_4_1_121 45 218 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 218 270 2 22 109 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 218 270 (accept_3_4 43 218 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 218 270 2 21 109 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 218 270 (Polychromatic418967fa.accept_22_19_20_6_1_8814 41 218 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 218 270 2 20 109 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 218 270
  (Polychromatic418967fa.accept_12_3_2_6_1_138 39 218 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 218 270 2 19 109 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 218 270 (accept_3_4 37 218 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 218 270 2 18 109 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 218 270 (Polychromatic418967fa.accept_19_16_9_4_1_9867 35 218 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 218 270 2 17 109 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 218 270
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 218 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 218 270 2 16 109 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 218 270 (accept_3_4 31 218 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 218 270 2 15 109 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 218 270 (Polychromatic418967fa.accept_16_13_10_14_1_2871 29 218 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 218 270 2 14 109 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 218 270
  (Polychromatic418967fa.accept_12_3_2_6_1_138 27 218 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 218 270 2 13 109 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 218 270 (accept_3_4 25 218 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 218 270 2 12 109 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 218 270 (Polychromatic418967fa.accept_16_7_10_14_1_1884 23 218 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 218 270 2 11 109 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 218 270
  (Polychromatic418967fa.accept_12_9_2_6_1_455 21 218 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 218 270 2 10 109 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 218 270 (accept_3_4 19 218 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 218 270 2 9 109 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 218 270 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 218 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 218 270 2 8 109 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 218 270
  (Polychromatic418967fa.accept_12_3_2_6_1_138 15 218 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 218 270 2 7 109 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 218 270 (accept_3_4 13 218 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 218 270 2 6 109 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 218 270 (Polychromatic418967fa.accept_14_11_8_4_1_2628 11 218 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 218 270 2 5 109 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 218 270
  (Polychromatic418967fa.accept_12_9_2_6_1_455 9 218 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 218 270 2 4 109 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 218 270 (accept_3_4 7 218 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 218 270 2 3 109 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 218 270 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 218 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 218 270 2 2 109 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 218 270
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 218 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 218 270 2 1 109 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 218 270 (accept_3_4 1 218 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 218
  270))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 217 270 (Eq.refl Bool.true)
  (allA_succ_of_accept 53 217 270 (accept_3_5 53 217 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 217 270 (Polychromatic418967fa.accept_14_10_7_4_1_3453 52 217 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 217 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 217 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 217 270 (accept_3_5 50 217 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 217 270 (Polychromatic418967fa.accept_20_9_17_10_1_3633 49 217 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 217 270
  (Polychromatic418967fa.accept_19_10_8_4_1_5626 48 217 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 217 270 (accept_3_5 47 217 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 217 270 (Polychromatic418967fa.accept_21_4_7_18_1_7561 46 217 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 217 270 (Polychromatic418967fa.accept_13_6_9_10_1_1201 45 217 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 217 270 (accept_3_5 44 217 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 217 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 217 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 217 270
  (Polychromatic418967fa.accept_17_8_13_15_1_2143 42 217 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 217 270 (accept_3_5 41 217 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 217 270 (Polychromatic418967fa.accept_13_1_9_10_1_625 40 217 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 217 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 217 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 217 270 (accept_3_5 38 217 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 217 270
  (Polychromatic418967fa.accept_16_5_9_14_1_5051 37 217 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 217 270 (Polychromatic418967fa.accept_11_3_8_6_1_788 36 217 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 217 270 (accept_3_5 35 217 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 217 270 (Polychromatic418967fa.accept_19_15_8_4_1_2962 34 217 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 217 270
  (Polychromatic418967fa.accept_19_14_8_4_1_2961 33 217 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 217 270 (accept_3_5 32 217 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 217 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 217 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 217 270 (Polychromatic418967fa.accept_21_9_7_18_1_1780 30 217 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 217 270 (accept_3_5 29 217 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 217 270 (Polychromatic418967fa.accept_17_11_13_15_1_2140 28
  217 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 217 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 217 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 217 270 (accept_3_5 26 217 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 217 270 (Polychromatic418967fa.accept_11_3_8_6_1_788 25 217 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 217 270 (Polychromatic418967fa.accept_14_10_7_4_1_3453 24 217 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 217 270 (accept_3_5 23 217 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 217 270 (Polychromatic418967fa.accept_17_5_13_15_1_5464 22 217
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 217 270
  (Polychromatic418967fa.accept_16_5_9_14_1_5051 21 217 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 217 270 (accept_3_5 20 217 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 217 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 217 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 217 270 (Polychromatic418967fa.accept_19_18_8_4_1_7069 18 217 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 217 270 (accept_3_5 17 217 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 217 270 (Polychromatic418967fa.accept_23_16_10_17_1_14852 16
  217 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 217 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 217 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 217 270 (accept_3_5 14 217 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 217 270 (Polychromatic418967fa.accept_19_13_8_4_1_7047 13 217 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 217 270 (Polychromatic418967fa.accept_13_12_9_10_1_1223 12 217 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 217 270 (accept_3_5 11 217 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 217 270 (Polychromatic418967fa.accept_14_10_7_4_1_3453 10 217
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 217 270
  (Polychromatic418967fa.accept_19_9_8_4_1_7046 9 217 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 217 270 (accept_3_5 8 217 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  217 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 217 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 217 270 (Polychromatic418967fa.accept_13_6_9_10_1_1201 6 217 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 217 270 (accept_3_5 5 217 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 217 270 (Polychromatic418967fa.accept_16_4_9_14_1_3883 4 217
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 217 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 217 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 217 270 (accept_3_5 2 217 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  217 270 (Polychromatic418967fa.accept_13_1_9_10_1_625 1 217 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 217 270)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 216 270 (Eq.refl
  Bool.true) (allA_succ_of_gcd 54 216 270 54 1 4 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 216 270 (Polychromatic418967fa.accept_21_11_6_18_1_4450 53 216 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 216 270 2 26 108 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 216 270 3 17 72 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 216 270 2 25 108 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 216 270
  (Polychromatic418967fa.accept_19_11_7_4_1_4308 49 216 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 216 270 6 8 36 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 216 270 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 216 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 216 270 2 23 108 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 216 270 9 5 24 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 216 270 2 22 108 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 216 270
  (Polychromatic418967fa.accept_13_4_8_10_1_671 43 216 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 216 270 6 7 36 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 216 270 (Polychromatic418967fa.accept_13_2_8_10_1_1902 41 216 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 216 270 2 20 108 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 216 270 3 13 72 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 216 270 2 19 108 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 216 270
  (Polychromatic418967fa.accept_7_2_6_4_1_29 37 216 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 216 270 18 2 12 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 216 270 (Polychromatic418967fa.accept_17_1_12_15_1_1263 35 216 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 216 270 2 17 108 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 216 270 3 11 72 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 216 270 2 16 108 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 216 270
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 216 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 216 270 6 5 36 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 216 270 (Polychromatic418967fa.accept_20_9_16_10_1_3559 29 216 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 216 270 2 14 108 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 216 270 27 1 8 10 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 216 270 2 13 108 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 216 270
  (Polychromatic418967fa.accept_13_12_8_10_1_1879 25 216 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 216 270 6 4 36 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 216 270 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 216 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 216 270 2 11 108 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 216 270 3 7 72 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 216 270 2 10 108 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 216 270
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 216 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 216 270 18 1 12 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 216 270 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 216 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 216 270 2 8 108 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 216 270 3 5 72 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 216 270 2 7 108 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 216 270
  (Polychromatic418967fa.accept_19_13_7_4_1_1869 13 216 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 216 270 6 2 36 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 216 270 (Polychromatic418967fa.accept_13_11_8_10_1_676 11 216 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 216 270 2 5 108 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 216 270 9 1 24 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 216 270 2 4 108 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 216 270
  (Polychromatic418967fa.accept_13_7_8_10_1_2663 7 216 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 216 270 6 1 36 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 216 270 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 216 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 216 270 2 2 108 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 216 270 3 1 72 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 216 270 2 1 108 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 216 270
  (Polychromatic418967fa.accept_11_1_7_6_1_378 1 216 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 216 270))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 215 270 (Eq.refl Bool.true)
  (allA_succ_of_gcd 55 215 270 5 11 43 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 54 215 270 (Polychromatic418967fa.accept_20_14_15_10_1_3554 54 215 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 215 270
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 215 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 215 270 (accept_3_4 52 215 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 215 270 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 215 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 215 270 5 10 43 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 215 270 (accept_3_4 49 215 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 215 270 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 215 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 215 270 (Polychromatic418967fa.accept_13_8_7_10_1_4362 47 215
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 215 270 (accept_3_4 46 215
  270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 215 270 5 9 43 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 215 270
  (Polychromatic418967fa.accept_7_2_5_4_1_115 44 215 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 215 270 (accept_3_4 43 215 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 215 270 (Polychromatic418967fa.accept_13_3_7_10_1_668 42 215 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 215 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 215 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 215 270 5 8 43 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 215 270
  (Polychromatic418967fa.accept_17_5_11_15_1_5445 39 215 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 215 270 (Polychromatic418967fa.accept_13_12_7_10_1_2662 38 215 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 215 270 (accept_3_4 37 215 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 215 270 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 215 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 215 270 5 7 43 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 215 270 (accept_3_4 34
  215 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 215 270
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 215 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 215 270 (Polychromatic418967fa.accept_19_13_6_4_1_4207 32 215 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 215 270 (accept_3_4 31 215 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 215 270 5 6 43 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 215 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 215 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 215 270 (accept_3_4 28 215 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 215 270 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 215 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 215 270
  (Polychromatic418967fa.accept_16_10_7_14_1_2882 26 215 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 215 270 5 5 43 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 24 215 270 (Polychromatic418967fa.accept_19_5_6_4_1_8480 24 215 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 215 270
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 215 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 215 270 (accept_3_4 22 215 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 215 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 215 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 215 270 5 4 43 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 215 270 (accept_3_4 19 215 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 215 270 (Polychromatic418967fa.accept_20_18_15_10_1_12414 18 215 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 215 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 17
  215 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 215 270 (accept_3_4 16
  215 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 215 270 5 3 43 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 215 270
  (Polychromatic418967fa.accept_20_14_15_10_1_3554 14 215 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 215 270 (accept_3_4 13 215 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 215 270 (Polychromatic418967fa.accept_13_12_7_10_1_2662 12 215 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 215 270
  (Polychromatic418967fa.accept_20_11_15_10_1_15111 11 215 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 215 270 5 2 43 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 215 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 215 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 215 270
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 215 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 215 270 (accept_3_4 7 215 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  215 270 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 215 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 5 215 270 5 1 43 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 4 215 270 (accept_3_4 4 215 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 215 270 (Polychromatic418967fa.accept_13_3_7_10_1_668 3 215 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 215 270 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 215 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 215 270 (accept_3_4 1 215 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 215 270))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 57 214 270 (Eq.refl Bool.true) (allA_succ_of_gcd 56 214 270 2 28 107 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 214 270
  (Polychromatic418967fa.accept_13_3_6_10_1_2658 55 214 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 214 270 2 27 107 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 214 270 (accept_3_5 53 214 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 214 270 2 26 107 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 214 270 (Polychromatic418967fa.accept_12_3_10_6_1_442 51 214 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 214 270 2 25 107 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 214 270
  (Polychromatic418967fa.accept_21_7_4_18_1_4471 49 214 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 214 270 2 24 107 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 214 270 (accept_3_5 47 214 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 214 270 2 23 107 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 214 270 (Polychromatic418967fa.accept_11_1_5_6_1_397 45 214 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 214 270 2 22 107 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 214 270
  (Polychromatic418967fa.accept_11_10_5_6_1_1842 43 214 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 214 270 2 21 107 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 214 270 (accept_3_5 41 214 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 214 270 2 20 107 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 214 270 (Polychromatic418967fa.accept_12_3_10_6_1_442 39 214 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 214 270 2 19 107 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 214 270
  (Polychromatic418967fa.accept_19_18_5_4_1_7042 37 214 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 214 270 2 18 107 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 214 270 (accept_3_5 35 214 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 214 270 2 17 107 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 214 270 (Polychromatic418967fa.accept_12_9_10_6_1_872 33 214 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 214 270 2 16 107 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 214 270
  (Polychromatic418967fa.accept_13_5_6_10_1_2659 31 214 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 214 270 2 15 107 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 214 270 (accept_3_5 29 214 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 214 270 2 14 107 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 214 270 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 214 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 214 270 2 13 107 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 214 270
  (Polychromatic418967fa.accept_13_12_6_10_1_667 25 214 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 214 270 2 12 107 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 214 270 (accept_3_5 23 214 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 214 270 2 11 107 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 214 270 (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 214 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 214 270 2 10 107 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 214 270
  (Polychromatic418967fa.accept_17_2_10_15_1_1238 19 214 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 214 270 2 9 107 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 214 270 (accept_3_5 17 214 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 214 270 2 8 107 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 214 270 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 214 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 214 270 2 7 107 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 214 270
  (Polychromatic418967fa.accept_21_13_4_18_1_7553 13 214 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 214 270 2 6 107 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 214 270 (accept_3_5 11 214 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 214 270 2 5 107 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 214 270 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 214 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 214 270 2 4 107 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 214 270
  (Polychromatic418967fa.accept_21_7_4_18_1_4471 7 214 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 214 270 2 3 107 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 214 270 (accept_3_5 5 214 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 214 270 2 2 107 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 214 270 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 214 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 214 270 2 1 107 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 214 270
  (Polychromatic418967fa.accept_11_1_5_6_1_397 1 214 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 214 270))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 213 270 (Eq.refl Bool.true)
  (allA_succ_of_gcd 57 213 270 3 19 71 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 213 270 (Polychromatic418967fa.accept_12_8_9_6_1_127 56 213 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 213 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 55
  213 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 213 270 3 18 71 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 213 270
  (Polychromatic418967fa.accept_21_11_3_18_1_3068 53 213 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 213 270 (Polychromatic418967fa.accept_12_4_9_6_1_440 52 213 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 213 270 3 17 71 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 213 270
  (Polychromatic418967fa.accept_7_1_3_4_1_128 50 213 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 213 270 (Polychromatic418967fa.accept_14_7_3_4_1_1816 49 213 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 213 270 3 16 71 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 213 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 47
  213 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 213 270
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 46 213 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 213 270 3 15 71 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 213 270 (Polychromatic418967fa.accept_12_8_9_6_1_127 44 213 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 213 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 43
  213 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 213 270 3 14 71 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 213 270
  (Polychromatic418967fa.accept_7_6_3_4_1_294 41 213 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 213 270 (Polychromatic418967fa.accept_12_4_9_6_1_440 40 213 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 213 270 3 13 71 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 213 270 (Polychromatic418967fa.accept_12_2_9_6_1_439
  38 213 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 213 270
  (Polychromatic418967fa.accept_20_17_13_10_1_5059 37 213 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 213 270 3 12 71 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 213 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 213 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 213 270
  (Polychromatic418967fa.accept_7_6_3_4_1_294 34 213 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 213 270 3 11 71 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 213 270 (Polychromatic418967fa.accept_12_8_9_6_1_127 32 213 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 213 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 31
  213 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 213 270 3 10 71 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 213 270
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 213 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 213 270 (Polychromatic418967fa.accept_12_4_9_6_1_440 28 213 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 213 270 3 9 71 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 213 270 (Polychromatic418967fa.accept_12_2_9_6_1_439
  26 213 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 213 270
  (Polychromatic418967fa.accept_16_9_5_14_1_6126 25 213 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 213 270 3 8 71 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 213 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 213 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 213 270 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 213 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 213 270 3 7 71 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 213 270
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 213 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 213 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 213 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 213 270 3 6 71 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 213 270 (Polychromatic418967fa.accept_13_4_5_10_1_1247
  17 213 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 213 270
  (Polychromatic418967fa.accept_12_4_9_6_1_440 16 213 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 213 270 3 5 71 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 213 270 (Polychromatic418967fa.accept_12_2_9_6_1_439 14 213 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 213 270 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 213 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 213 270 3 4 71 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 213 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 213 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 213 270 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 213 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 213 270 3 3 71 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 213 270 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 213 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 213 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 213 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 213 270 3 2 71 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 213 270 (Polychromatic418967fa.accept_20_5_13_10_1_15100 5 213 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 213 270 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 213 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 213 270 3 1 71 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 213 270
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 2 213 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 213 270 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 213 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 213 270))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 59 212 270 (Eq.refl Bool.true) (allA_succ_of_gcd 58 212 270 2 29 106 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 212 270
  (Polychromatic418967fa.accept_12_9_8_6_1_466 57 212 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 212 270 2 28 106 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 212 270 (accept_3_4 55 212 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 212 270 2 27 106 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 212 270 (Polychromatic418967fa.accept_11_9_3_6_1_797 53 212 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 212 270 2 26 106 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 212 270
  (Polychromatic418967fa.accept_12_3_8_6_1_895 51 212 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 212 270 2 25 106 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 212 270 (accept_3_4 49 212 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 212 270 2 24 106 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 212 270 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 212 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 212 270 2 23 106 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 212 270
  (Polychromatic418967fa.accept_12_9_8_6_1_466 45 212 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 212 270 2 22 106 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 212 270 (accept_3_4 43 212 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 212 270 2 21 106 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 212 270 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 212 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 212 270 2 20 106 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 212 270
  (Polychromatic418967fa.accept_12_3_8_6_1_895 39 212 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 212 270 2 19 106 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 212 270 (accept_3_4 37 212 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 212 270 2 18 106 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 212 270 (Polychromatic418967fa.accept_19_16_3_4_1_4281 35 212 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 212 270 2 17 106 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 212 270
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 212 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 212 270 2 16 106 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 212 270 (accept_3_4 31 212 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 212 270 2 15 106 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 212 270 (Polychromatic418967fa.accept_25_4_12_20_1_11348 29 212 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 212 270 2 14 106 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 212 270
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 212 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 212 270 2 13 106 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 212 270 (accept_3_4 25 212 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 212 270 2 12 106 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 212 270 (Polychromatic418967fa.accept_14_9_2_4_1_1814 23 212 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 212 270 2 11 106 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 212 270
  (Polychromatic418967fa.accept_12_9_8_6_1_466 21 212 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 212 270 2 10 106 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 212 270 (accept_3_4 19 212 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 212 270 2 9 106 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 212 270 (Polychromatic418967fa.accept_16_1_4_14_1_1896 17 212 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 212 270 2 8 106 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 212 270
  (Polychromatic418967fa.accept_12_3_8_6_1_895 15 212 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 212 270 2 7 106 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 212 270 (accept_3_4 13 212 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 212 270 2 6 106 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 212 270 (Polychromatic418967fa.accept_13_11_4_10_1_3440 11 212 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 212 270 2 5 106 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 212 270
  (Polychromatic418967fa.accept_11_9_3_6_1_797 9 212 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 212 270 2 4 106 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 212 270 (accept_3_4 7 212 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 212 270 2 3 106 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 212 270 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 212 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 212 270 2 2 106 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 212 270
  (Polychromatic418967fa.accept_12_3_8_6_1_895 3 212 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 212 270 2 1 106 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 212 270 (accept_3_4 1 212 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 212
  270))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 211 270 (Eq.refl Bool.true)
  (allA_succ_of_accept 59 211 270 (accept_3_5 59 211 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 211 270 (Polychromatic418967fa.accept_13_6_3_10_1_698 58 211 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 211 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 211 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 211 270 (accept_3_5 56 211 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 211 270 (Polychromatic418967fa.accept_19_17_2_4_1_4278 55 211 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 211 270
  (Polychromatic418967fa.accept_7_5_1_4_1_122 54 211 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 211 270 (accept_3_5 53 211 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 211 270 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 211 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 211 270 (Polychromatic418967fa.accept_21_9_1_18_1_1761 51 211 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 211 270 (accept_3_5 50 211 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 211 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 211 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 211 270
  (Polychromatic418967fa.accept_11_4_2_6_1_389 48 211 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 211 270 (accept_3_5 47 211 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 211 270 (Polychromatic418967fa.accept_13_7_3_10_1_656 46 211 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 211 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 211 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 211 270 (accept_3_5 44 211 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 211 270 (Polychromatic418967fa.accept_16_11_3_14_1_5043 43 211 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 211 270
  (Polychromatic418967fa.accept_22_20_13_6_1_10490 42 211 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 211 270 (accept_3_5 41 211 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 211 270 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 211 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 211 270 (Polychromatic418967fa.accept_14_11_1_4_1_4445 39 211
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 211 270 (accept_3_5 38 211
  270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 211 270 (Polychromatic418967fa.accept_4_1_3_2_1_3
  37 211 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 211 270
  (Polychromatic418967fa.accept_17_2_7_15_1_5525 36 211 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 211 270 (accept_3_5 35 211 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 211 270 (Polychromatic418967fa.accept_20_14_11_10_1_11036 34 211 270 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 211 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 211 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 211 270 (accept_3_5 32 211 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 211 270 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 211 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 211 270
  (Polychromatic418967fa.accept_19_11_2_4_1_8443 30 211 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 211 270 (accept_3_5 29 211 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 211 270 (Polychromatic418967fa.accept_13_2_3_10_1_658 28 211 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 211 270 (Polychromatic418967fa.accept_16_11_3_14_1_5043 27 211 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 211 270 (accept_3_5 26 211 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 211 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 211 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 211 270
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 211 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 211 270 (accept_3_5 23 211 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 211 270 (Polychromatic418967fa.accept_17_5_7_15_1_1230 22 211 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 211 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 211 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 211 270 (accept_3_5 20 211 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 211 270 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 211 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 211 270
  (Polychromatic418967fa.accept_19_18_2_4_1_7039 18 211 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 211 270 (accept_3_5 17 211 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 211 270 (Polychromatic418967fa.accept_19_16_2_4_1_8512 16 211 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 211 270 (Polychromatic418967fa.accept_11_4_2_6_1_389 15 211 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 211 270 (accept_3_5 14 211 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 211 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 211 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 211 270
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 211 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 211 270 (accept_3_5 11 211 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 211 270 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 211 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 211 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 211 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 211 270 (accept_3_5 8 211 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 211 270 (Polychromatic418967fa.accept_13_7_3_10_1_656 7 211 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 211 270
  (Polychromatic418967fa.accept_13_6_3_10_1_698 6 211 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 211 270 (accept_3_5 5 211 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  211 270 (Polychromatic418967fa.accept_11_4_2_6_1_389 4 211 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 211 270 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 211 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 211 270 (accept_3_5 2 211 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 211 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 211 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 211
  270)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 210 270 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 210 270 30 2 7 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 210 270 (Polychromatic418967fa.accept_17_8_6_15_1_523 59 210 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 210 270 2 29 105 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 210 270 3 19 70 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 210 270 2 28 105 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 210 270 5 11 42 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 210 270 6 9 35 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 210 270
  (Polychromatic418967fa.accept_19_15_1_4_1_4238 53 210 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 210 270 2 26 105 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 210 270 3 17 70 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 50 210 270 10 5 21 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 210 270 (Polychromatic418967fa.accept_11_5_1_6_1_774 49 210 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 210 270 6 8 35 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 210 270
  (Polychromatic418967fa.accept_13_8_2_10_1_652 47 210 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 210 270 2 23 105 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 210 270 15 3 14 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 210 270 2 22 105 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 210 270 (Polychromatic418967fa.accept_17_9_6_15_1_5454 43 210
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 210 270 6 7 35 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 210 270
  (Polychromatic418967fa.accept_19_3_1_4_1_1860 41 210 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 210 270 10 4 21 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 210 270 3 13 70 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 210 270 2 19 105 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 210 270 (Polychromatic418967fa.accept_13_11_2_10_1_4399 37 210
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 210 270 6 6 35 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 210 270 5 7 42 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 210 270 2 17 105 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 210 270 3 11 70
  90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 210 270 2 16
  105 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 210
  270 (Polychromatic418967fa.accept_13_5_2_10_1_248 31 210 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 210 270 30 1 7 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 210 270 (Polychromatic418967fa.accept_11_7_1_6_1_1281 29 210 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 210 270 2 14 105 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 210 270 3 9 70 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 210 270 2 13 105 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 210 270 5 5 42 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 210 270 6 4 35 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 210 270
  (Polychromatic418967fa.accept_24_23_18_6_1_16565 23 210 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 210 270 2 11 105 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 21 210 270 3 7 70 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 20 210 270 10 2 21 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 210 270 (Polychromatic418967fa.accept_13_6_2_10_1_1240 19 210
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 210 270 6 3 35 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 210 270
  (Polychromatic418967fa.accept_19_17_1_4_1_7022 17 210 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 210 270 2 8 105 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 210 270 15 1 14 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 14 210 270 2 7 105 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 210 270 (Polychromatic418967fa.accept_23_13_3_17_1_14989 13 210
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 210 270 6 2 35 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 210 270
  (Polychromatic418967fa.accept_13_11_2_10_1_4399 11 210 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 210 270 10 1 21 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 210 270 3 3 70 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 8 210 270 2 4 105 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 210 270 (Polychromatic418967fa.accept_11_7_1_6_1_1281 7 210 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 210 270 6 1 35 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 210 270 5 1 42 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 210 270 2 2 105 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 210 270 3 1 70 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 210 270 2 1 105 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 210 270
  (Polychromatic418967fa.accept_24_1_18_6_1_6211 1 210 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 210 270))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 209 270 (Eq.refl
  Bool.true) (allA_succ_of_accept 61 209 270 (accept_3_4 61 209 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 209 270 (Polychromatic418967fa.accept_22_16_11_6_1_16534 60 209 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 209 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 59
  209 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 209 270 (accept_3_4 58
  209 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 209 270
  (Polychromatic418967fa.accept_20_17_9_10_1_12382 57 209 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 209 270 (Polychromatic418967fa.accept_13_4_1_10_1_693 56 209 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 209 270 (accept_3_4 55 209 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 209 270 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 209 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 209 270
  (Polychromatic418967fa.accept_20_13_9_10_1_8083 53 209 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 209 270 (accept_3_4 52 209 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 209 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 209 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 209 270 (Polychromatic418967fa.accept_13_11_1_10_1_648 50 209
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 209 270 (accept_3_4 49 209
  270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 209 270
  (Polychromatic418967fa.accept_13_9_1_10_1_647 48 209 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 209 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 209 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 209 270 (accept_3_4 46 209 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 209 270 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 209 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 209 270 (Polychromatic418967fa.accept_7_2_6_4_1_29 44
  209 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 209 270 (accept_3_4 43
  209 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 209 270
  (Polychromatic418967fa.accept_22_20_11_6_1_13497 42 209 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 209 270 (Polychromatic418967fa.accept_17_7_5_15_1_3184 41 209 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 209 270 (accept_3_4 40 209 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 209 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 209 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 209 270
  (Polychromatic418967fa.accept_7_3_6_4_1_30 38 209 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 209 270 (accept_3_4 37 209 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 209 270 (Polychromatic418967fa.accept_16_4_1_14_1_3908 36 209 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 209 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 209 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 209 270 (accept_3_4 34 209 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 209 270 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 209 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 209 270
  (Polychromatic418967fa.accept_21_11_20_18_1_7656 32 209 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 209 270 (accept_3_4 31 209 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 209 270 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 209 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 209 270 (Polychromatic418967fa.accept_16_13_1_14_1_2855 29 209
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 209 270 (accept_3_4 28 209
  270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 209 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 209 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 209 270 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 209 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 209 270 (accept_3_4 25 209 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 209 270 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 209 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 209 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 23
  209 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 209 270 (accept_3_4 22
  209 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 209 270
  (Polychromatic418967fa.accept_20_1_9_10_1_6491 21 209 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 209 270 (Polychromatic418967fa.accept_16_4_1_14_1_3908 20 209 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 209 270 (accept_3_4 19 209 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 209 270 (Polychromatic418967fa.accept_22_18_11_6_1_8763 18 209 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 209 270
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 209 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 209 270 (accept_3_4 16 209 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 209 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 209 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 209 270 (Polychromatic418967fa.accept_21_14_20_18_1_9174 14 209 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 209 270 (accept_3_4 13 209 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 209 270 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 209 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 209 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 209 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 209 270 (accept_3_4 10 209 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  209 270 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 209 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 209 270 (Polychromatic418967fa.accept_23_8_2_17_1_13334 8 209 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 209 270 (accept_3_4 7 209 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 209 270 (Polychromatic418967fa.accept_20_6_9_10_1_8024 6 209
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 209 270
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 209 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 209 270 (accept_3_4 4 209 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  209 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 209 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 209 270 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 209 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 209 270 (accept_3_4 1 209 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 209 270)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63
  208 270 (Eq.refl Bool.true) (allA_succ_of_gcd 62 208 270 2 31 104 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 208 270 (Polychromatic418967fa.accept_17_10_4_15_1_2165 61 208
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 208 270 2 30 104 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 208 270 (accept_3_5 59
  208 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 208 270 2 29 104 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 208 270
  (Polychromatic418967fa.accept_7_1_5_4_1_134 57 208 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 208 270 2 28 104 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 208 270 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 208 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 208 270 2 27 104 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 208 270 (accept_3_5 53 208 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 208 270 2 26 104 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 208 270 (Polychromatic418967fa.accept_7_2_5_4_1_115 51
  208 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 208 270 2 25 104 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 208 270
  (Polychromatic418967fa.accept_11_5_10_6_1_793 49 208 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 208 270 2 24 104 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 208 270 (accept_3_5 47 208 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 208 270 2 23 104 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 208 270 (Polychromatic418967fa.accept_12_9_4_6_1_460 45 208 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 208 270 2 22 104 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 208 270
  (Polychromatic418967fa.accept_7_1_5_4_1_134 43 208 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 208 270 2 21 104 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 208 270 (accept_3_5 41 208 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 208 270 2 20 104 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 208 270 (Polychromatic418967fa.accept_12_3_4_6_1_434 39 208 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 208 270 2 19 104 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 208 270
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 208 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 208 270 2 18 104 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 208 270 (accept_3_5 35 208 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 208 270 2 17 104 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 208 270 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 208 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 208 270 2 16 104 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 208 270
  (Polychromatic418967fa.accept_25_6_8_20_1_16564 31 208 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 208 270 2 15 104 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 208 270 (accept_3_5 29 208 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 208 270 2 14 104 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 208 270 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 208 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 208 270 2 13 104 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 208 270
  (Polychromatic418967fa.accept_20_5_8_10_1_11026 25 208 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 208 270 2 12 104 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 208 270 (accept_3_5 23 208 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 208 270 2 11 104 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 208 270 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 208 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 208 270 2 10 104 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 208 270
  (Polychromatic418967fa.accept_17_2_4_15_1_5451 19 208 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 208 270 2 9 104 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 208 270 (accept_3_5 17 208 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 208 270 2 8 104 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 208 270 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 208 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 208 270 2 7 104 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 208 270
  (Polychromatic418967fa.accept_7_6_5_4_1_297 13 208 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 208 270 2 6 104 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 208 270 (accept_3_5 11 208 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 208 270 2 5 104 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 208 270 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 208 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 208 270 2 4 104 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 208 270
  (Polychromatic418967fa.accept_20_7_8_10_1_11025 7 208 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 208 270 2 3 104 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 208 270 (accept_3_5 5 208 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 208 270 2 2 104 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 208 270 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 208 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 208 270 2 1 104 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 208 270
  (Polychromatic418967fa.accept_7_1_5_4_1_134 1 208 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 208 270))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 207 270 (Eq.refl
  Bool.true) (allA_succ_of_gcd 63 207 270 9 7 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 207 270 (Polychromatic418967fa.accept_12_2_3_6_1_112 62 207 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 207 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 61
  207 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 207 270 3 20 69 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 207 270
  (Polychromatic418967fa.accept_13_7_12_10_1_640 59 207 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 207 270 (Polychromatic418967fa.accept_11_3_9_6_1_105 58 207 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 207 270 3 19 69 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 207 270 (Polychromatic418967fa.accept_12_8_3_6_1_909
  56 207 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 207 270
  (Polychromatic418967fa.accept_16_7_15_14_1_2889 55 207 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 207 270 9 6 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 207 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 207 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 207 270
  (Polychromatic418967fa.accept_12_4_3_6_1_879 52 207 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 207 270 3 17 69 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 207 270 (Polychromatic418967fa.accept_12_2_3_6_1_112 50 207 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 207 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 49
  207 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 207 270 3 16 69 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 207 270
  (Polychromatic418967fa.accept_11_3_9_6_1_105 47 207 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 207 270 (Polychromatic418967fa.accept_12_10_3_6_1_882 46 207 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 207 270 9 5 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 207 270 (Polychromatic418967fa.accept_12_8_3_6_1_909
  44 207 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 207 270
  (Polychromatic418967fa.accept_14_1_11_4_1_3430 43 207 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 207 270 3 14 69 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 207 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 207 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 207 270 (Polychromatic418967fa.accept_12_4_3_6_1_879
  40 207 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 207 270 3 13 69 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 207 270
  (Polychromatic418967fa.accept_12_2_3_6_1_112 38 207 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 207 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 207 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 207 270 9 4 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 207 270 (Polychromatic418967fa.accept_13_9_12_10_1_242
  35 207 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 207 270
  (Polychromatic418967fa.accept_12_10_3_6_1_882 34 207 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 207 270 3 11 69 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 207 270 (Polychromatic418967fa.accept_12_8_3_6_1_909 32 207 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 207 270
  (Polychromatic418967fa.accept_17_14_3_15_1_5449 31 207 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 207 270 3 10 69 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 207 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 207 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 207 270
  (Polychromatic418967fa.accept_12_4_3_6_1_879 28 207 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 207 270 9 3 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 207 270 (Polychromatic418967fa.accept_12_2_3_6_1_112 26 207 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 207 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 207 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 207 270 3 8 69 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 207 270
  (Polychromatic418967fa.accept_16_7_15_14_1_2889 23 207 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 207 270 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 207 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 207 270 3 7 69 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 207 270
  (Polychromatic418967fa.accept_12_8_3_6_1_909 20 207 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 207 270 (Polychromatic418967fa.accept_13_6_12_10_1_690 19 207 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 207 270 9 2 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 207 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 17
  207 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 207 270
  (Polychromatic418967fa.accept_12_4_3_6_1_879 16 207 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 207 270 3 5 69 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 207 270 (Polychromatic418967fa.accept_11_3_9_6_1_105 14 207 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 207 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 207 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 207 270 3 4 69 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 207 270
  (Polychromatic418967fa.accept_13_11_12_10_1_2652 11 207 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 207 270 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 207 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 207 270 9 1 23 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 207 270
  (Polychromatic418967fa.accept_12_8_3_6_1_909 8 207 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 207 270 (Polychromatic418967fa.accept_13_7_12_10_1_640 7 207 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 207 270 3 2 69 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 207 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 207 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 207 270
  (Polychromatic418967fa.accept_12_4_3_6_1_879 4 207 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 207 270 3 1 69 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 207 270 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 207 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 207 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 207 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 207
  270)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 206 270 (Eq.refl Bool.true)
  (allA_succ_of_gcd 64 206 270 2 32 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 206 270 (Polychromatic418967fa.accept_12_3_2_6_1_138 63 206 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 206 270 2 31 103 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 206 270 (accept_3_4 61 206 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 206 270 2 30 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 206 270 (Polychromatic418967fa.accept_19_2_16_4_1_8525
  59 206 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 206 270 2 29 103 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 206 270
  (Polychromatic418967fa.accept_7_1_3_4_1_128 57 206 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 206 270 2 28 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 206 270 (accept_3_4 55 206 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 206 270 2 27 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 206 270 (Polychromatic418967fa.accept_13_1_11_10_1_1258 53 206 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 206 270 2 26 103 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 206 270
  (Polychromatic418967fa.accept_12_3_2_6_1_138 51 206 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 206 270 2 25 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 206 270 (accept_3_4 49 206 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 206 270 2 24 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 206 270 (Polychromatic418967fa.accept_11_3_8_6_1_788 47 206 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 206 270 2 23 103 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 206 270
  (Polychromatic418967fa.accept_12_9_2_6_1_455 45 206 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 206 270 2 22 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 206 270 (accept_3_4 43 206 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 206 270 2 21 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 206 270 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 206 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 206 270 2 20 103 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 206 270
  (Polychromatic418967fa.accept_12_3_2_6_1_138 39 206 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 206 270 2 19 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 206 270 (accept_3_4 37 206 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 206 270 2 18 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 206 270 (Polychromatic418967fa.accept_14_7_10_4_1_130 35 206 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 206 270 2 17 103 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 206 270
  (Polychromatic418967fa.accept_12_9_2_6_1_455 33 206 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 206 270 2 16 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 206 270 (accept_3_4 31 206 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 206 270 2 15 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 206 270 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 206 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 206 270 2 14 103 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 206 270
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 206 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 206 270 2 13 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 206 270 (accept_3_4 25 206 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 206 270 2 12 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 206 270 (Polychromatic418967fa.accept_26_23_24_10_1_12936 23 206 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 206 270 2 11 103 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 206 270
  (Polychromatic418967fa.accept_12_9_2_6_1_455 21 206 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 206 270 2 10 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 206 270 (accept_3_4 19 206 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 206 270 2 9 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 206 270 (Polychromatic418967fa.accept_13_4_11_10_1_1226 17 206 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 206 270 2 8 103 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 206 270
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 206 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 206 270 2 7 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 206 270 (accept_3_4 13 206 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 206 270 2 6 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 206 270 (Polychromatic418967fa.accept_19_11_16_4_1_7075 11 206 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 206 270 2 5 103 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 206 270
  (Polychromatic418967fa.accept_12_9_2_6_1_455 9 206 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 206 270 2 4 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 206 270 (accept_3_4 7 206 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 206 270 2 3 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 206 270 (Polychromatic418967fa.accept_20_5_6_10_1_3536 5 206 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 206 270 2 2 103 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 206 270
  (Polychromatic418967fa.accept_11_3_8_6_1_788 3 206 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 206 270 2 1 103 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 206 270 (accept_3_4 1 206 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 206
  270))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 205 270 (Eq.refl Bool.true)
  (allA_succ_of_gcd 65 205 270 5 13 41 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 64 205 270 (Polychromatic418967fa.accept_20_4_5_10_1_2308 64 205 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 205 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 205 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 205 270 (accept_3_5 62 205 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 205 270 (Polychromatic418967fa.accept_7_5_2_4_1_126 61 205 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 205 270 5 12 41 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 205 270 (accept_3_5 59 205 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 205 270 (Polychromatic418967fa.accept_14_2_9_4_1_1735 58 205 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 205 270 (Polychromatic418967fa.accept_20_17_5_10_1_3591 57 205
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 205 270 (accept_3_5 56 205
  270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 205 270 5 11 41 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 205 270
  (Polychromatic418967fa.accept_7_5_2_4_1_126 54 205 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 205 270 (accept_3_5 53 205 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 205 270 (Polychromatic418967fa.accept_19_14_15_4_1_11248 52 205 270 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 205 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 205 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 205 270 5 10 41 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 205 270
  (Polychromatic418967fa.accept_16_1_13_14_1_1064 49 205 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 205 270 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 205 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 205 270 (accept_3_5 47 205 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 205 270 (Polychromatic418967fa.accept_17_12_1_15_1_5472 46 205 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 205 270 5 9 41 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 205 270 (accept_3_5 44
  205 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 205 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 205 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 205 270 (Polychromatic418967fa.accept_16_10_13_14_1_5042 42 205 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 205 270 (accept_3_5 41 205 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 205 270 5 8 41 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 205 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 205 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 205 270 (accept_3_5 38 205 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 205 270
  (Polychromatic418967fa.accept_17_3_1_15_1_6835 37 205 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 205 270 (Polychromatic418967fa.accept_20_16_5_10_1_6487 36 205 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 205 270 5 7 41 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 205 270
  (Polychromatic418967fa.accept_7_6_2_4_1_291 34 205 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 205 270 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 205 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 205 270 (accept_3_5 32 205 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 205 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 205 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 205 270 5 6 41 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 205 270 (accept_3_5 29 205 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 205 270 (Polychromatic418967fa.accept_19_9_15_4_1_5613 28 205
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 205 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 205 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 205 270 (accept_3_5 26 205 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  205 270 5 5 41 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 205 270 (Polychromatic418967fa.accept_19_5_15_4_1_4224 24 205 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 205 270 (accept_3_5 23 205 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 205 270 (Polychromatic418967fa.accept_20_2_5_10_1_3535 22 205 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 205 270 (Polychromatic418967fa.accept_20_1_5_10_1_3534 21 205
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 205 270 5 4 41 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 205 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 205 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 205 270 (Polychromatic418967fa.accept_19_18_15_4_1_9838 18 205 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 205 270 (accept_3_5 17 205 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 205 270 (Polychromatic418967fa.accept_14_2_9_4_1_1735 16 205 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 205 270 5 3 41 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 205 270 (accept_3_5 14 205 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 205 270 (Polychromatic418967fa.accept_7_6_2_4_1_291
  13 205 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 205 270
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 205 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 205 270 (accept_3_5 11 205 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  205 270 5 2 41 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 205 270 (Polychromatic418967fa.accept_17_9_1_15_1_3156 9 205 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 205 270 (accept_3_5 8 205 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 205 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 205 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 205 270 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 205 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 205 270 5 1 41 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 205 270
  (Polychromatic418967fa.accept_20_4_5_10_1_2308 4 205 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 205 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 205 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 205 270 (accept_3_5 2 205 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 205 270 (Polychromatic418967fa.accept_11_1_7_6_1_378 1 205 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 205
  270)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 204 270 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 204 270 6 11 34 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 204 270 (Polychromatic418967fa.accept_19_8_14_4_1_2967 65 204 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 204 270 2 32 102 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 204 270 3 21 68 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 204 270 2 31 102 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 204 270
  (Polychromatic418967fa.accept_7_5_1_4_1_122 61 204 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 204 270 6 10 34 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 204 270 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 204 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 204 270 2 29 102 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 204 270 3 19 68 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 204 270 2 28 102 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 204 270
  (Polychromatic418967fa.accept_20_15_4_10_1_9538 55 204 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 204 270 6 9 34 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 204 270 (Polychromatic418967fa.accept_13_1_9_10_1_625 53 204 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 204 270 2 26 102 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 204 270 3 17 68 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 204 270 2 25 102 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 204 270
  (Polychromatic418967fa.accept_21_7_15_18_1_7526 49 204 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 204 270 6 8 34 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 204 270 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 204 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 204 270 2 23 102 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 204 270 3 15 68 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 204 270 2 22 102 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 204 270
  (Polychromatic418967fa.accept_21_1_15_18_1_7646 43 204 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 204 270 6 7 34 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 204 270 (Polychromatic418967fa.accept_20_1_4_10_1_3645 41 204 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 204 270 2 20 102 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 204 270 3 13 68 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 204 270 2 19 102 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 204 270
  (Polychromatic418967fa.accept_19_18_14_4_1_8517 37 204 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 204 270 6 6 34 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 204 270 (Polychromatic418967fa.accept_20_15_4_10_1_9538 35 204 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 204 270 2 17 102 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 204 270 3 11 68 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 204 270 2 16 102
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 204 270
  (Polychromatic418967fa.accept_7_3_1_4_1_121 31 204 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 204 270 6 5 34 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 204 270 (Polychromatic418967fa.accept_19_10_14_4_1_7072 29 204 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 204 270 2 14 102 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 204 270 3 9 68 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 204 270 2 13 102 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 204 270
  (Polychromatic418967fa.accept_13_12_9_10_1_1223 25 204 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 204 270 6 4 34 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 204 270 (Polychromatic418967fa.accept_21_2_15_18_1_806 23 204 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 204 270 2 11 102 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 204 270 3 7 68 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 204 270 2 10 102 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 204 270
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 204 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 204 270 6 3 34 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 204 270 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 204 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 204 270 2 8 102 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 204 270 3 5 68 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 204 270 2 7 102 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 204 270
  (Polychromatic418967fa.accept_19_13_14_4_1_5621 13 204 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 204 270 6 2 34 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 204 270 (Polychromatic418967fa.accept_14_11_8_4_1_2628 11 204 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 204 270 2 5 102 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 204 270 3 3 68 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 204 270 2 4 102 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 204 270
  (Polychromatic418967fa.accept_19_7_14_4_1_4268 7 204 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 204 270 6 1 34 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 204 270 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 204 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 204 270 2 2 102 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 204 270 3 1 68 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 204 270 2 1 102 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 204 270
  (Polychromatic418967fa.accept_13_1_9_10_1_625 1 204 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 204 270))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 203 270 (Eq.refl
  Bool.true) (allA_succ_of_accept 67 203 270 (accept_3_4 67 203 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 203 270 (Polychromatic418967fa.accept_14_10_7_4_1_3453 66 203 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 203 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 203 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 203 270 (accept_3_4 64 203 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 203 270
  (Polychromatic418967fa.accept_13_11_8_10_1_676 63 203 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 203 270 (Polychromatic418967fa.accept_17_11_16_15_1_5467 62 203 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 203 270 (accept_3_4 61 203 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 203 270 (Polychromatic418967fa.accept_19_3_13_4_1_9856 60 203 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 203 270
  (Polychromatic418967fa.accept_13_7_8_10_1_2663 59 203 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 203 270 (accept_3_4 58 203 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 203 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 203 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 203 270 (Polychromatic418967fa.accept_11_1_5_6_1_397 56 203 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 203 270 (accept_3_4 55 203 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 203 270 (Polychromatic418967fa.accept_11_10_5_6_1_1842 54 203
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 203 270
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 203 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 203 270 (accept_3_4 52 203 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 203 270 (Polychromatic418967fa.accept_13_12_8_10_1_1879 51 203 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 203 270 (Polychromatic418967fa.accept_13_11_8_10_1_676 50 203 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 203 270 (accept_3_4 49 203 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 203 270 (Polychromatic418967fa.accept_17_14_16_15_1_5509 48
  203 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 203 270
  (Polychromatic418967fa.accept_19_9_13_4_1_2982 47 203 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 203 270 (accept_3_4 46 203 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 203 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 203 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 203 270 (Polychromatic418967fa.accept_13_5_8_10_1_4363 44 203 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 203 270 (accept_3_4 43 203 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 203 270 (Polychromatic418967fa.accept_20_2_3_10_1_5075 42 203
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 203 270
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 203 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 203 270 (accept_3_4 40 203 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 203 270 (Polychromatic418967fa.accept_14_11_7_4_1_3449 39 203 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 203 270 (Polychromatic418967fa.accept_13_12_8_10_1_1879 38 203 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 203 270 (accept_3_4 37 203 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 203 270 (Polychromatic418967fa.accept_19_17_13_4_1_7081 36 203
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 203 270
  (Polychromatic418967fa.accept_16_3_11_14_1_446 35 203 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 203 270 (accept_3_4 34 203 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 203 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 203 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 203 270 (Polychromatic418967fa.accept_11_10_5_6_1_1842 32 203 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 203 270 (accept_3_4 31 203 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 203 270 (Polychromatic418967fa.accept_13_4_8_10_1_671 30 203
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 203 270
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 203 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 203 270 (accept_3_4 28 203 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 203 270 (Polychromatic418967fa.accept_19_8_13_4_1_15140 27 203 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 203 270 (Polychromatic418967fa.accept_19_7_13_4_1_1824 26 203 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 203 270 (accept_3_4 25 203 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 203 270 (Polychromatic418967fa.accept_13_11_8_10_1_676 24 203
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 203 270
  (Polychromatic418967fa.accept_11_1_5_6_1_397 23 203 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 203 270 (accept_3_4 22 203 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 203 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 203 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 203 270 (Polychromatic418967fa.accept_13_7_8_10_1_2663 20 203 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 203 270 (accept_3_4 19 203 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 203 270 (Polychromatic418967fa.accept_13_5_8_10_1_4363 18 203
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 203 270
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 203 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 203 270 (accept_3_4 16 203 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 203 270 (Polychromatic418967fa.accept_13_2_8_10_1_1902 15 203 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 203 270 (Polychromatic418967fa.accept_17_14_16_15_1_5509 14 203 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 203 270 (accept_3_4 13 203 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 203 270 (Polychromatic418967fa.accept_11_1_5_6_1_397 12 203
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 203 270
  (Polychromatic418967fa.accept_13_11_8_10_1_676 11 203 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 203 270 (accept_3_4 10 203 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  203 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 203 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 203 270 (Polychromatic418967fa.accept_19_8_13_4_1_15140 8 203 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 203 270 (accept_3_4 7 203 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 203 270 (Polychromatic418967fa.accept_19_6_13_4_1_876 6 203 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 203 270
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 203 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 203 270 (accept_3_4 4 203 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  203 270 (Polychromatic418967fa.accept_14_3_7_4_1_118 3 203 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 203 270 (Polychromatic418967fa.accept_13_2_8_10_1_1902 2 203 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 203 270 (accept_3_4 1 203 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 203 270))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 69 202 270 (Eq.refl Bool.true) (allA_succ_of_gcd 68 202 270 2 34 101 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 202 270
  (Polychromatic418967fa.accept_21_4_13_18_1_137 67 202 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 202 270 2 33 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 202 270 (accept_3_5 65 202 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 202 270 2 32 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 202 270 (Polychromatic418967fa.accept_12_3_10_6_1_442 63 202 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 202 270 2 31 101 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 202 270
  (Polychromatic418967fa.accept_7_5_6_4_1_117 61 202 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 202 270 2 30 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 202 270 (accept_3_5 59 202 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 202 270 2 29 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 202 270 (Polychromatic418967fa.accept_11_2_4_6_1_2412 57 202 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 202 270 2 28 101 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 202 270
  (Polychromatic418967fa.accept_13_3_7_10_1_668 55 202 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 202 270 2 27 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 202 270 (accept_3_5 53 202 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 202 270 2 26 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 202 270 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 202 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 202 270 2 25 101 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 202 270
  (Polychromatic418967fa.accept_19_11_12_4_1_8455 49 202 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 202 270 2 24 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 202 270 (accept_3_5 47 202 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 202 270 2 23 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 202 270 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 202 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 202 270 2 22 101 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 202 270
  (Polychromatic418967fa.accept_13_4_7_10_1_1200 43 202 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 202 270 2 21 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 202 270 (accept_3_5 41 202 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 202 270 2 20 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 202 270 (Polychromatic418967fa.accept_12_3_10_6_1_442 39 202 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 202 270 2 19 101 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 202 270
  (Polychromatic418967fa.accept_7_2_6_4_1_29 37 202 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 202 270 2 18 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 202 270 (accept_3_5 35 202 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 202 270 2 17 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 202 270 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 202 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 202 270 2 16 101 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 202 270
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 202 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 202 270 2 15 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 202 270 (accept_3_5 29 202 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 202 270 2 14 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 202 270 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 202 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 202 270 2 13 101 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 202 270
  (Polychromatic418967fa.accept_13_12_7_10_1_2662 25 202 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 202 270 2 12 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 202 270 (accept_3_5 23 202 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 202 270 2 11 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 202 270 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 202 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 202 270 2 10 101 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 202 270
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 202 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 202 270 2 9 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 202 270 (accept_3_5 17 202 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 202 270 2 8 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 202 270 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 202 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 202 270 2 7 101 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 202 270
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 13 202 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 202 270 2 6 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 202 270 (accept_3_5 11 202 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 202 270 2 5 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 202 270 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 202 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 202 270 2 4 101 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 202 270
  (Polychromatic418967fa.accept_16_7_10_14_1_1884 7 202 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 202 270 2 3 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 202 270 (accept_3_5 5 202 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 202 270 2 2 101 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 202 270 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 202 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 202 270 2 1 101 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 202 270
  (Polychromatic418967fa.accept_19_1_12_4_1_4263 1 202 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 202 270))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 201 270 (Eq.refl
  Bool.true) (allA_succ_of_gcd 69 201 270 3 23 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 68 201 270 (Polychromatic418967fa.accept_12_8_9_6_1_127 68 201 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 201 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 67 201 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 201 270 3 22 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 201 270 (Polychromatic418967fa.accept_7_2_5_4_1_115 65 201 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 201 270 (Polychromatic418967fa.accept_7_1_5_4_1_134
  64 201 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 201 270 3 21 67 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 201 270
  (Polychromatic418967fa.accept_7_6_5_4_1_297 62 201 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 201 270 (Polychromatic418967fa.accept_13_9_6_10_1_666 61 201 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 201 270 3 20 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 201 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 59
  201 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 201 270
  (Polychromatic418967fa.accept_7_2_5_4_1_115 58 201 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 201 270 3 19 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 201 270 (Polychromatic418967fa.accept_12_8_9_6_1_127 56 201 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 201 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 55
  201 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 201 270 3 18 67 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 201 270
  (Polychromatic418967fa.accept_11_9_3_6_1_797 53 201 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 201 270 (Polychromatic418967fa.accept_11_8_3_6_1_1855 52 201 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 201 270 3 17 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 201 270 (Polychromatic418967fa.accept_7_1_5_4_1_134 50
  201 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 201 270
  (Polychromatic418967fa.accept_20_9_1_10_1_6466 49 201 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 201 270 3 16 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 201 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 201 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 201 270
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 46 201 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 201 270 3 15 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 201 270 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 201 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 201 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 43
  201 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 201 270 3 14 67 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 201 270
  (Polychromatic418967fa.accept_7_6_5_4_1_297 41 201 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 201 270 (Polychromatic418967fa.accept_12_4_9_6_1_440 40 201 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 201 270 3 13 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 201 270 (Polychromatic418967fa.accept_12_2_9_6_1_439
  38 201 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 201 270
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 201 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 201 270 3 12 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 201 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 201 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 201 270 (Polychromatic418967fa.accept_7_6_5_4_1_297
  34 201 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 201 270 3 11 67 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 201 270
  (Polychromatic418967fa.accept_12_8_9_6_1_127 32 201 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 201 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 201 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 201 270 3 10 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 201 270 (Polychromatic418967fa.accept_7_1_5_4_1_134 29
  201 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 201 270
  (Polychromatic418967fa.accept_12_4_9_6_1_440 28 201 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 201 270 3 9 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 201 270 (Polychromatic418967fa.accept_12_2_9_6_1_439 26 201 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 201 270 (Polychromatic418967fa.accept_13_12_6_10_1_667 25 201
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 201 270 3 8 67 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 201 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 201 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 201 270 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 201 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 201 270 3 7 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 201 270 (Polychromatic418967fa.accept_7_6_5_4_1_297 20
  201 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 201 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 201 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 201 270 3 6 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 201 270 (Polychromatic418967fa.accept_13_4_6_10_1_1199 17 201 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 201 270 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 201 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 201 270 3 5 67 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 201 270
  (Polychromatic418967fa.accept_12_2_9_6_1_439 14 201 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 201 270 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 201 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 201 270 3 4 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 201 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 11
  201 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 201 270
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 201 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 201 270 3 3 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 201 270 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 201 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 201 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 201 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 201 270 3 2 67 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 201 270
  (Polychromatic418967fa.accept_13_5_6_10_1_2659 5 201 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 201 270 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 201 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 201 270 3 1 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 201 270 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 201 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 201 270
  (Polychromatic418967fa.accept_7_1_5_4_1_134 1 201 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 201 270)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 200 270
  (Eq.refl Bool.true) (allA_succ_of_gcd 70 200 270 10 7 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 200 270 (Polychromatic418967fa.accept_12_9_8_6_1_466 69 200 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 200 270 2 34 100 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 200 270 (accept_3_4 67
  200 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 200 270 2 33 100 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 200 270 5 13 40 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 200 270 2 32 100 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 200 270
  (Polychromatic418967fa.accept_12_3_8_6_1_895 63 200 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 200 270 2 31 100 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 200 270 (accept_3_4 61 200 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 200 270 10 6 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 200 270 (Polychromatic418967fa.accept_11_4_2_6_1_389 59 200 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 200 270 2 29 100 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 200 270
  (Polychromatic418967fa.accept_12_9_8_6_1_466 57 200 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 200 270 2 28 100 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 55 200 270 5 11 40 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 200 270 2 27 100 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 200 270 (Polychromatic418967fa.accept_17_2_13_15_1_4349 53 200
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 200 270 2 26 100 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 200 270
  (Polychromatic418967fa.accept_12_3_8_6_1_895 51 200 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 200 270 10 5 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 200 270 (accept_3_4 49 200 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 200 270 2 24 100 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 200 270 (Polychromatic418967fa.accept_13_8_5_10_1_2701 47 200 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 200 270 2 23 100 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 200 270 5 9 40 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 200 270 2 22 100 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 200 270 (accept_3_4 43
  200 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 200 270 2 21 100 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 200 270
  (Polychromatic418967fa.accept_13_2_5_10_1_250 41 200 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 200 270 10 4 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 200 270 (Polychromatic418967fa.accept_12_3_8_6_1_895 39 200 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 200 270 2 19 100 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 200 270 (accept_3_4 37 200 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 200 270 2 18 100 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 200 270 5 7 40 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 200 270 2 17 100 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 200 270
  (Polychromatic418967fa.accept_12_9_8_6_1_466 33 200 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 200 270 2 16 100 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 200 270 (accept_3_4 31 200 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 200 270 10 3 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 200 270 (Polychromatic418967fa.accept_21_8_11_18_1_15050 29 200 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 200 270 2 14 100 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 200 270
  (Polychromatic418967fa.accept_12_3_8_6_1_895 27 200 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 200 270 2 13 100 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 25 200 270 5 5 40 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 200 270 2 12 100 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 200 270 (Polychromatic418967fa.accept_22_1_2_6_1_5427 23 200 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 200 270 2 11 100 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 200 270
  (Polychromatic418967fa.accept_12_9_8_6_1_466 21 200 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 200 270 10 2 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 200 270 (accept_3_4 19 200 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 200 270 2 9 100 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 200 270 (Polychromatic418967fa.accept_13_4_5_10_1_1247 17 200 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 200 270 2 8 100 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 200 270 5 3 40 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 200 270 2 7 100 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 200 270 (accept_3_4 13
  200 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 200 270 2 6 100 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 200 270
  (Polychromatic418967fa.accept_17_11_13_15_1_2140 11 200 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 200 270 10 1 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 200 270 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 200 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 200 270 2 4 100 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 200 270 (accept_3_4 7 200 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 200 270 2 3 100 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 200 270 5 1 40 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 200 270 2 2 100 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 200 270
  (Polychromatic418967fa.accept_12_3_8_6_1_895 3 200 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 200 270 2 1 100 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 200 270 (accept_3_4 1 200 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 200
  270))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 199 270 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 199 270 (accept_3_5 71 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 199 270 (Polychromatic418967fa.accept_13_5_4_10_1_1244 70 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 199 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 199 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 199 270 (accept_3_5 68 199 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 199 270 (Polychromatic418967fa.accept_19_10_9_4_1_5620 67 199 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 199 270
  (Polychromatic418967fa.accept_13_1_4_10_1_622 66 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 199 270 (accept_3_5 65 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 199 270 (Polychromatic418967fa.accept_7_1_3_4_1_128 64 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 199 270 (Polychromatic418967fa.accept_13_11_4_10_1_3440 63 199 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 199 270 (accept_3_5 62 199 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 199 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 199 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 199 270
  (Polychromatic418967fa.accept_11_5_1_6_1_774 60 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 199 270 (accept_3_5 59 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 199 270 (Polychromatic418967fa.accept_13_6_4_10_1_660 58 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 199 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 199 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 199 270 (accept_3_5 56 199 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 199 270 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 199 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 199 270
  (Polychromatic418967fa.accept_17_3_12_15_1_1203 54 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 199 270 (accept_3_5 53 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 199 270 (Polychromatic418967fa.accept_16_4_7_14_1_3897 52 199 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 199 270 (Polychromatic418967fa.accept_11_7_1_6_1_1281 51 199
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 199 270 (accept_3_5 50 199
  270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 199 270 (Polychromatic418967fa.accept_4_1_3_2_1_3
  49 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 199 270
  (Polychromatic418967fa.accept_7_6_3_4_1_294 48 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 199 270 (accept_3_5 47 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 199 270 (Polychromatic418967fa.accept_13_7_4_10_1_2675 46 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 199 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 199 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 199 270 (accept_3_5 44 199 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 199 270 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 199 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 199 270
  (Polychromatic418967fa.accept_16_10_7_14_1_2882 42 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 199 270 (accept_3_5 41 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 199 270 (Polychromatic418967fa.accept_11_7_1_6_1_1281 40 199 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 199 270 (Polychromatic418967fa.accept_22_17_1_6_1_15031 39 199
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 199 270 (accept_3_5 38 199
  270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 199 270 (Polychromatic418967fa.accept_4_1_3_2_1_3
  37 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 199 270
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 199 270 (accept_3_5 35 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 199 270 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 199 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 199 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 199 270 (accept_3_5 32 199 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 199 270 (Polychromatic418967fa.accept_13_5_4_10_1_1244 31 199 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 199 270
  (Polychromatic418967fa.accept_21_9_10_18_1_7567 30 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 199 270 (accept_3_5 29 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 199 270 (Polychromatic418967fa.accept_21_7_10_18_1_16563 28 199 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 199 270 (Polychromatic418967fa.accept_7_6_3_4_1_294
  27 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 199 270 (accept_3_5 26
  199 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 199 270
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 199 270 (Polychromatic418967fa.accept_13_11_4_10_1_3440 24 199 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 199 270 (accept_3_5 23 199 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 199 270 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 199 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 199 270
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 199 270 (accept_3_5 20 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 199 270 (Polychromatic418967fa.accept_13_6_4_10_1_660 19 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 199 270 (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 199 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 199 270 (accept_3_5 17 199 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 199 270 (Polychromatic418967fa.accept_11_5_1_6_1_774 16 199
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 199 270
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 199 270 (accept_3_5 14 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 199 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 199 270 (Polychromatic418967fa.accept_24_12_7_6_1_6244 12 199 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 199 270 (accept_3_5 11 199 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 199 270 (Polychromatic418967fa.accept_16_10_7_14_1_2882 10 199
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 199 270
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 199 270 (accept_3_5 8 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  199 270 (Polychromatic418967fa.accept_11_7_1_6_1_1281 7 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 199 270 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 199 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 199 270 (accept_3_5 5 199 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 199 270 (Polychromatic418967fa.accept_16_4_7_14_1_3897 4 199 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 199 270
  (Polychromatic418967fa.accept_17_3_12_15_1_1203 3 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 199 270 (accept_3_5 2 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  199 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 199 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 199 270)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73
  198 270 (Eq.refl Bool.true) (allA_succ_of_gcd 72 198 270 18 4 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 198 270 (Polychromatic418967fa.accept_13_6_3_10_1_698 71 198
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 198 270 2 35 99 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 198 270 3 23 66 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 198 270 2 34 99
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 198 270
  (Polychromatic418967fa.accept_13_2_3_10_1_658 67 198 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 198 270 6 11 33 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 198 270 (Polychromatic418967fa.accept_14_9_2_4_1_1814 65 198 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 198 270 2 32 99 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 198 270 9 7 22 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 198 270 2 31 99 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 198 270
  (Polychromatic418967fa.accept_7_5_2_4_1_126 61 198 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 198 270 6 10 33 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 198 270 (Polychromatic418967fa.accept_13_7_3_10_1_656 59 198 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 198 270 2 29 99 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 198 270 3 19 66 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 198 270 2 28 99 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 198 270
  (Polychromatic418967fa.accept_7_6_2_4_1_291 55 198 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 198 270 18 3 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 198 270 (Polychromatic418967fa.accept_19_15_8_4_1_2962 53 198 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 198 270 2 26 99 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 198 270 3 17 66 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 198 270 2 25 99 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 198 270
  (Polychromatic418967fa.accept_21_7_9_18_1_7519 49 198 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 198 270 6 8 33 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 198 270 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 198 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 198 270 2 23 99 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 198 270 9 5 22 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 198 270 2 22 99 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 198 270
  (Polychromatic418967fa.accept_19_5_8_4_1_4289 43 198 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 198 270 6 7 33 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 198 270 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 198 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 198 270 2 20 99 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 198 270 3 13 66 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 198 270 2 19 99 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 198 270
  (Polychromatic418967fa.accept_13_11_3_10_1_4374 37 198 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 198 270 18 2 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 198 270 (Polychromatic418967fa.accept_20_15_18_10_1_8067 35 198 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 198 270 2 17 99 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 198 270 3 11 66 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 198 270 2 16 99
  135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 198 270
  (Polychromatic418967fa.accept_19_12_8_4_1_8514 31 198 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 198 270 6 5 33 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 198 270 (Polychromatic418967fa.accept_19_10_8_4_1_5626 29 198 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 198 270 2 14 99 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 198 270 9 3 22 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 198 270 2 13 99 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 198 270
  (Polychromatic418967fa.accept_20_5_18_10_1_3565 25 198 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 198 270 6 4 33 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 198 270 (Polychromatic418967fa.accept_14_9_2_4_1_1814 23 198 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 198 270 2 11 99 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 198 270 3 7 66 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 198 270 2 10 99 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 198 270
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 198 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 198 270 18 1 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 198 270 (Polychromatic418967fa.accept_19_17_8_4_1_4212 17 198 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 198 270 2 8 99 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 198 270 3 5 66 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 198 270 2 7 99 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 198 270
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 198 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 198 270 6 2 33 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 198 270 (Polychromatic418967fa.accept_13_11_3_10_1_4374 11 198 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 198 270 2 5 99 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 198 270 9 1 22 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 198 270 2 4 99 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 198 270
  (Polychromatic418967fa.accept_13_7_3_10_1_656 7 198 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 198 270 6 1 33 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 198 270 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 198 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 198 270 2 2 99 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 198 270 3 1 66 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 198 270 2 1 99 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 198 270 (Polychromatic418967fa.accept_21_1_9_18_1_4428
  1 198 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 198
  270))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 197 270 (Eq.refl
  Bool.true) (allA_succ_of_accept 73 197 270 (accept_3_4 73 197 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 197 270 (Polychromatic418967fa.accept_17_4_10_15_1_5444 72 197 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 197 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 71
  197 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 197 270 (accept_3_4 70
  197 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 197 270
  (Polychromatic418967fa.accept_19_12_7_4_1_9873 69 197 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 197 270 (Polychromatic418967fa.accept_7_5_1_4_1_122 68 197 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 197 270 (accept_3_4 67 197 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 197 270 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 197 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 197 270
  (Polychromatic418967fa.accept_20_5_17_10_1_3632 65 197 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 197 270 (accept_3_4 64 197 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 197 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 197 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 197 270 (Polychromatic418967fa.accept_24_14_5_6_1_11512 62 197
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 197 270 (accept_3_4 61 197
  270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 197 270
  (Polychromatic418967fa.accept_11_5_10_6_1_793 60 197 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 197 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 197 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 197 270 (accept_3_4 58 197 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 197 270 (Polychromatic418967fa.accept_13_5_2_10_1_248 57 197 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 197 270
  (Polychromatic418967fa.accept_17_5_10_15_1_5574 56 197 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 197 270 (accept_3_4 55 197 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 197 270 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 197 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 197 270 (Polychromatic418967fa.accept_14_11_1_4_1_4445 53 197
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 197 270 (accept_3_4 52 197
  270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 197 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 197 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 197 270 (Polychromatic418967fa.accept_13_11_2_10_1_4399 50 197 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 197 270 (accept_3_4 49 197 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 197 270 (Polychromatic418967fa.accept_20_8_17_10_1_8016 48 197 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 197 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 197 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 197 270 (accept_3_4 46 197 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 197 270 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 197 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 197 270 (Polychromatic418967fa.accept_13_5_2_10_1_248 44 197 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 197 270 (accept_3_4 43 197 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 197 270 (Polychromatic418967fa.accept_13_3_2_10_1_2697 42 197
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 197 270
  (Polychromatic418967fa.accept_16_9_5_14_1_6126 41 197 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 197 270 (accept_3_4 40 197 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 197 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 197 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 197 270 (Polychromatic418967fa.accept_7_3_1_4_1_121 38 197 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 197 270 (accept_3_4 37 197 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 197 270 (Polychromatic418967fa.accept_17_2_10_15_1_1238 36 197 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 197 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 197 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 197 270 (accept_3_4 34 197 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 197 270 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 197 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 197 270 (Polychromatic418967fa.accept_13_6_2_10_1_1240 32 197 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 197 270 (accept_3_4 31 197 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 197 270 (Polychromatic418967fa.accept_19_11_7_4_1_4308 30 197
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 197 270
  (Polychromatic418967fa.accept_13_3_2_10_1_2697 29 197 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 197 270 (accept_3_4 28 197 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 197 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 197 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 197 270 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 197 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 197 270 (accept_3_4 25 197 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 197 270 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 197 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 197 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 197 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 197 270 (accept_3_4 22 197 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 197 270 (Polychromatic418967fa.accept_13_8_2_10_1_652 21 197 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 197 270 (Polychromatic418967fa.accept_19_1_7_4_1_9842 20 197 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 197 270 (accept_3_4 19 197 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 197 270 (Polychromatic418967fa.accept_13_5_2_10_1_248 18 197
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 197 270
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 197 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 197 270 (accept_3_4 16 197 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 197 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 197 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 197 270 (Polychromatic418967fa.accept_19_14_7_4_1_4210 14 197 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 197 270 (accept_3_4 13 197 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 197 270 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 197 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 197 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 197 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 197 270 (accept_3_4 10 197 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  197 270 (Polychromatic418967fa.accept_16_9_5_14_1_6126 9 197 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 197 270 (Polychromatic418967fa.accept_13_8_2_10_1_652 8 197 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 197 270 (accept_3_4 7 197 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 197 270 (Polychromatic418967fa.accept_13_6_2_10_1_1240 6 197 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 197 270
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 197 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 197 270 (accept_3_4 4 197 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  197 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 197 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 197 270 (Polychromatic418967fa.accept_17_2_10_15_1_1238 2 197 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 197 270 (accept_3_4 1 197 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 197
  270)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 196 270 (Eq.refl
  Bool.true) (allA_succ_of_gcd 74 196 270 2 37 98 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 196 270 (Polychromatic418967fa.accept_16_9_4_14_1_1878 73 196 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 196 270 2 36 98 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 196 270 (accept_3_5 71 196 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 196 270 2 35 98 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 196 270
  (Polychromatic418967fa.accept_11_3_9_6_1_105 69 196 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 196 270 2 34 98 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 196 270 (Polychromatic418967fa.accept_19_10_6_4_1_16473 67 196 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 196 270 2 33 98 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 196 270 (accept_3_5 65 196 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 196 270 2 32 98 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 196 270
  (Polychromatic418967fa.accept_12_3_4_6_1_434 63 196 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 196 270 2 31 98 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 196 270 (Polychromatic418967fa.accept_13_9_1_10_1_647 61 196 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 196 270 2 30 98 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 196 270 (accept_3_5 59 196 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 196 270 2 29 98 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 196 270
  (Polychromatic418967fa.accept_12_9_4_6_1_460 57 196 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 196 270 2 28 98 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 196 270 (Polychromatic418967fa.accept_16_7_4_14_1_2860 55 196 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 196 270 2 27 98 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 196 270 (accept_3_5 53 196 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 196 270 2 26 98 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 196 270
  (Polychromatic418967fa.accept_12_3_4_6_1_434 51 196 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 196 270 2 25 98 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 196 270 (Polychromatic418967fa.accept_16_1_4_14_1_1896 49 196 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 196 270 2 24 98 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 196 270 (accept_3_5 47 196 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 196 270 2 23 98 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 196 270
  (Polychromatic418967fa.accept_12_9_4_6_1_460 45 196 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 196 270 2 22 98 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 196 270 (Polychromatic418967fa.accept_13_4_1_10_1_693 43 196 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 196 270 2 21 98 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 196 270 (accept_3_5 41 196 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 196 270 2 20 98 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 196 270
  (Polychromatic418967fa.accept_12_3_4_6_1_434 39 196 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 196 270 2 19 98 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 196 270 (Polychromatic418967fa.accept_13_11_1_10_1_648 37 196 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 196 270 2 18 98 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 196 270 (accept_3_5 35 196 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 196 270 2 17 98 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 196 270
  (Polychromatic418967fa.accept_12_9_4_6_1_460 33 196 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 196 270 2 16 98 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 196 270 (Polychromatic418967fa.accept_16_15_4_14_1_6123 31 196 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 196 270 2 15 98 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 196 270 (accept_3_5 29 196 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 196 270 2 14 98 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 196 270
  (Polychromatic418967fa.accept_12_3_4_6_1_434 27 196 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 196 270 2 13 98 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 196 270 (Polychromatic418967fa.accept_11_3_9_6_1_105 25 196 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 196 270 2 12 98 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 196 270 (accept_3_5 23 196 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 196 270 2 11 98 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 196 270 (Polychromatic418967fa.accept_12_9_4_6_1_460
  21 196 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 196 270 2 10 98 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 196 270
  (Polychromatic418967fa.accept_20_19_16_10_1_12445 19 196 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 196 270 2 9 98 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 196 270 (accept_3_5 17 196 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 196 270 2 8 98 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 196 270 (Polychromatic418967fa.accept_12_3_4_6_1_434 15 196 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 196 270 2 7 98 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 196 270
  (Polychromatic418967fa.accept_19_13_6_4_1_4207 13 196 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 196 270 2 6 98 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 196 270 (accept_3_5 11 196 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 196 270 2 5 98 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 196 270 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 196 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 196 270 2 4 98 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 196 270
  (Polychromatic418967fa.accept_16_7_4_14_1_2860 7 196 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 196 270 2 3 98 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 196 270 (accept_3_5 5 196 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 196
  270 2 2 98 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  196 270 (Polychromatic418967fa.accept_11_3_9_6_1_105 3 196 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 196 270 2 1 98 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 196 270 (Polychromatic418967fa.accept_16_1_4_14_1_1896 1 196 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 196
  270))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 195 270 (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 195 270 15 5 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 195 270 (Polychromatic418967fa.accept_12_2_3_6_1_112 74 195 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 195 270
  (Polychromatic418967fa.accept_4_1_3_2_1_3 73 195 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 195 270 3 24 65 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 195 270 (Polychromatic418967fa.accept_20_11_15_10_1_15111 71 195 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 195 270 5 14 39 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 195 270 3 23 65 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 195 270
  (Polychromatic418967fa.accept_7_5_6_4_1_117 68 195 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 195 270 (Polychromatic418967fa.accept_20_7_15_10_1_3628 67 195 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 195 270 3 22 65 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 195 270 5 13 39 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 195 270
  (Polychromatic418967fa.accept_12_4_3_6_1_879 64 195 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 195 270 3 21 65 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 195 270 (Polychromatic418967fa.accept_12_2_3_6_1_112 62 195 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 195 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 61
  195 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 195 270 15 4 13 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 195 270
  (Polychromatic418967fa.accept_7_3_6_4_1_30 59 195 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 195 270 (Polychromatic418967fa.accept_7_2_6_4_1_29 58 195 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 195 270 3 19 65 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 195 270 (Polychromatic418967fa.accept_12_8_3_6_1_909
  56 195 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 195 270 5 11 39 54
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 195 270 3 18 65
  90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 195 270
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 195 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 195 270 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 195 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 195 270 3 17 65 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 195 270 5 10 39 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 195 270
  (Polychromatic418967fa.accept_4_1_3_2_1_3 49 195 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 195 270 3 16 65 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 195 270 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 195 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 195 270 (Polychromatic418967fa.accept_12_10_3_6_1_882
  46 195 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 195 270 15 3 13 18
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 195 270
  (Polychromatic418967fa.accept_7_2_6_4_1_29 44 195 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 195 270 (Polychromatic418967fa.accept_16_11_3_14_1_5043 43 195 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 195 270 3 14 65 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 195 270
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 195 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 195 270 5 8 39 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 195 270 3 13 65 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 195 270 (Polychromatic418967fa.accept_7_3_6_4_1_30 38 195 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 195 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 37
  195 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 195 270 3 12 65 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 195 270 5 7 39 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 195 270
  (Polychromatic418967fa.accept_12_10_3_6_1_882 34 195 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 195 270 3 11 65 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 195 270 (Polychromatic418967fa.accept_12_8_3_6_1_909 32 195 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 195 270 (Polychromatic418967fa.accept_7_3_6_4_1_30 31
  195 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 195 270 15 2 13 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 195 270
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 195 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 195 270 (Polychromatic418967fa.accept_12_4_3_6_1_879 28 195 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 195 270 3 9 65 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 195 270 (Polychromatic418967fa.accept_7_5_6_4_1_117 26
  195 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 195 270 5 5 39 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 195 270 3 8 65 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 195 270
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 195 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 195 270 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 195 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 195 270 3 7 65 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 195 270 5 4 39 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 195 270 (Polychromatic418967fa.accept_7_5_6_4_1_117 19
  195 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 195 270 3 6 65 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 195 270
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 195 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 195 270 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 195 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 195 270 15 1 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 195 270 (Polychromatic418967fa.accept_11_3_8_6_1_788
  14 195 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 195 270
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 195 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 195 270 3 4 65 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 195 270 (Polychromatic418967fa.accept_16_11_3_14_1_5043 11 195 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 195 270 5 2 39 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 195 270 3 3 65 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 195 270
  (Polychromatic418967fa.accept_12_8_3_6_1_909 8 195 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 195 270 (Polychromatic418967fa.accept_20_7_15_10_1_3628 7 195 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 195 270 3 2 65 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 195 270 5 1 39 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 195 270 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 195 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 195 270 3 1 65 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 195 270
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 195 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 195 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 195 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 195
  270)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 194 270 (Eq.refl
  Bool.true) (allA_succ_of_gcd 76 194 270 2 38 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 194 270 (Polychromatic418967fa.accept_12_3_2_6_1_138 75 194 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 194 270 2 37 97 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 194 270 (accept_3_4 73 194 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 194 270 2 36 97 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 194 270
  (Polychromatic418967fa.accept_7_1_5_4_1_134 71 194 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 194 270 2 35 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 194 270 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 194 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 194 270 2 34 97 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 194 270 (accept_3_4 67 194 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 194 270 2 33 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 194 270 (Polychromatic418967fa.accept_7_2_5_4_1_115 65
  194 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 194 270 2 32 97 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 194 270
  (Polychromatic418967fa.accept_12_3_2_6_1_138 63 194 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 194 270 2 31 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 194 270 (accept_3_4 61 194 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 194 270 2 30 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 194 270 (Polychromatic418967fa.accept_13_7_12_10_1_640 59 194 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 194 270 2 29 97 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 194 270
  (Polychromatic418967fa.accept_7_1_5_4_1_134 57 194 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 194 270 2 28 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 194 270 (accept_3_4 55 194 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 194 270 2 27 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 194 270 (Polychromatic418967fa.accept_17_2_7_15_1_5525 53 194 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 194 270 2 26 97 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 194 270
  (Polychromatic418967fa.accept_7_2_5_4_1_115 51 194 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 194 270 2 25 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 194 270 (accept_3_4 49 194 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 194 270 2 24 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 194 270 (Polychromatic418967fa.accept_13_8_12_10_1_4414 47 194 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 194 270 2 23 97 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 194 270
  (Polychromatic418967fa.accept_11_1_7_6_1_378 45 194 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 194 270 2 22 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 194 270 (accept_3_4 43 194 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 194 270 2 21 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 194 270 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 194 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 194 270 2 20 97 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 194 270
  (Polychromatic418967fa.accept_12_3_2_6_1_138 39 194 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 194 270 2 19 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 194 270 (accept_3_4 37 194 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 194 270 2 18 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 194 270 (Polychromatic418967fa.accept_13_9_12_10_1_242 35 194 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 194 270 2 17 97 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 194 270
  (Polychromatic418967fa.accept_12_9_2_6_1_455 33 194 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 194 270 2 16 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 194 270 (accept_3_4 31 194 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 194 270 2 15 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 194 270 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 194 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 194 270 2 14 97 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 194 270
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 194 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 194 270 2 13 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 194 270 (accept_3_4 25 194 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 194 270 2 12 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 194 270 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 194 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 194 270 2 11 97 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 194 270
  (Polychromatic418967fa.accept_12_9_2_6_1_455 21 194 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 194 270 2 10 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 194 270 (accept_3_4 19 194 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 194 270 2 9 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 194 270 (Polychromatic418967fa.accept_25_17_19_20_1_14763 17 194 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 194 270 2 8 97 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 194 270
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 194 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 194 270 2 7 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 194 270 (accept_3_4 13 194 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 194 270 2 6 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 194 270 (Polychromatic418967fa.accept_13_11_12_10_1_2652 11 194 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 194 270 2 5 97 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 194 270
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 194 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 194 270 2 4 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 194 270 (accept_3_4 7 194 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 194
  270 2 3 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  194 270 (Polychromatic418967fa.accept_17_5_7_15_1_1230 5 194 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 194 270 2 2 97 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 194 270 (Polychromatic418967fa.accept_12_3_2_6_1_138 3 194 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 194 270 2 1 97 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 194 270 (accept_3_4 1 194 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 194
  270))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 78 193 270 (Eq.refl
  Bool.true) (allA_succ_of_accept 77 193 270 (accept_3_5 77 193 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 193 270 (Polychromatic418967fa.accept_17_8_6_15_1_523 76 193 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 193 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 193 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 193 270 (accept_3_5 74 193 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 193 270
  (Polychromatic418967fa.accept_13_8_11_10_1_636 73 193 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 193 270 (Polychromatic418967fa.accept_20_12_13_10_1_8061 72 193 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 193 270 (accept_3_5 71 193 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 193 270 (Polychromatic418967fa.accept_19_13_3_4_1_15146 70 193 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 193 270
  (Polychromatic418967fa.accept_13_4_11_10_1_1226 69 193 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 193 270 (accept_3_5 68 193 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 193 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 193 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 193 270 (Polychromatic418967fa.accept_13_1_11_10_1_1258 66 193
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 193 270 (accept_3_5 65 193
  270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 193 270
  (Polychromatic418967fa.accept_13_12_11_10_1_2711 64 193 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 193 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 193 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 193 270 (accept_3_5 62 193 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 193 270 (Polychromatic418967fa.accept_16_13_1_14_1_2855 61 193 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 193 270
  (Polychromatic418967fa.accept_13_8_11_10_1_636 60 193 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 193 270 (accept_3_5 59 193 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 193 270 (Polychromatic418967fa.accept_19_1_3_4_1_4306 58 193 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 193 270 (Polychromatic418967fa.accept_14_1_11_4_1_3430 57 193 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 193 270 (accept_3_5 56 193 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 193 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 193 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 193 270
  (Polychromatic418967fa.accept_13_2_11_10_1_1881 54 193 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 193 270 (accept_3_5 53 193 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 193 270 (Polychromatic418967fa.accept_16_4_1_14_1_3908 52 193 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 193 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 193 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 193 270 (accept_3_5 50 193 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 193 270
  (Polychromatic418967fa.accept_14_7_11_4_1_3455 49 193 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 193 270 (Polychromatic418967fa.accept_17_14_6_15_1_3151 48 193 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 193 270 (accept_3_5 47 193 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 193 270 (Polychromatic418967fa.accept_19_8_3_4_1_9865 46 193 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 193 270
  (Polychromatic418967fa.accept_16_13_1_14_1_2855 45 193 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 193 270 (accept_3_5 44 193 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 193 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 193 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 193 270 (Polychromatic418967fa.accept_13_3_11_10_1_2647 42 193
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 193 270 (accept_3_5 41 193
  270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 193 270
  (Polychromatic418967fa.accept_13_1_11_10_1_1258 40 193 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 193 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 193 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 193 270 (accept_3_5 38 193 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 193 270 (Polychromatic418967fa.accept_19_18_3_4_1_7079 37 193 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 193 270
  (Polychromatic418967fa.accept_14_8_11_4_1_3438 36 193 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 193 270 (accept_3_5 35 193 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 193 270 (Polychromatic418967fa.accept_13_8_11_10_1_636 34 193 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 193 270 (Polychromatic418967fa.accept_21_12_4_18_1_4424 33 193 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 193 270 (accept_3_5 32 193 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 193 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 193 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 193 270
  (Polychromatic418967fa.accept_13_4_11_10_1_1226 30 193 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 193 270 (accept_3_5 29 193 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 193 270 (Polychromatic418967fa.accept_13_2_11_10_1_1881 28 193 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 193 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 27
  193 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 193 270 (accept_3_5 26
  193 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 193 270
  (Polychromatic418967fa.accept_13_12_11_10_1_2711 25 193 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 193 270 (Polychromatic418967fa.accept_21_3_4_18_1_7617 24 193 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 193 270 (accept_3_5 23 193 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 193 270 (Polychromatic418967fa.accept_14_8_11_4_1_3438 22 193
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 193 270
  (Polychromatic418967fa.accept_13_8_11_10_1_636 21 193 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 193 270 (accept_3_5 20 193 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 193 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 193 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 193 270 (Polychromatic418967fa.accept_19_18_3_4_1_7079 18 193 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 193 270 (accept_3_5 17 193 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 193 270 (Polychromatic418967fa.accept_13_3_11_10_1_2647 16 193
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 193 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 193 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 193 270 (accept_3_5 14 193 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 193 270 (Polychromatic418967fa.accept_16_13_1_14_1_2855 13 193 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 193 270 (Polychromatic418967fa.accept_13_12_11_10_1_2711 12 193 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 193 270 (accept_3_5 11 193 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 193 270 (Polychromatic418967fa.accept_22_10_17_6_1_7104 10 193
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 193 270
  (Polychromatic418967fa.accept_17_9_6_15_1_5454 9 193 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 193 270 (accept_3_5 8 193 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  193 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 193 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 193 270 (Polychromatic418967fa.accept_19_6_3_4_1_7040 6 193 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 193 270 (accept_3_5 5 193 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 193 270 (Polychromatic418967fa.accept_13_4_11_10_1_1226 4 193 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 193 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 193 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 193 270 (accept_3_5 2 193 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  193 270 (Polychromatic418967fa.accept_13_1_11_10_1_1258 1 193 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 193 270))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 79 192 270 (Eq.refl Bool.true) (allA_succ_of_gcd 78 192 270 6 13 32 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 192 270
  (Polychromatic418967fa.accept_14_7_10_4_1_130 77 192 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 192 270 2 38 96 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 192 270 3 25 64 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 74 192 270 2 37 96 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 192 270 (Polychromatic418967fa.accept_19_16_2_4_1_8512 73 192
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 192 270 6 12 32 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 192 270
  (Polychromatic418967fa.accept_7_1_3_4_1_128 71 192 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 192 270 2 35 96 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 69 192 270 3 23 64 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 68 192 270 2 34 96 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 192 270 (Polychromatic418967fa.accept_11_1_5_6_1_397 67 192 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 192 270 6 11 32 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 192 270
  (Polychromatic418967fa.accept_11_10_5_6_1_1842 65 192 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 192 270 2 32 96 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 63 192 270 3 21 64 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 62 192 270 2 31 96 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 192 270 (Polychromatic418967fa.accept_17_10_5_15_1_4332 61 192
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 192 270 6 10 32 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 192 270
  (Polychromatic418967fa.accept_21_17_3_18_1_7549 59 192 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 192 270 2 29 96 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 57 192 270 3 19 64 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 192 270 2 28 96 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 192 270 (Polychromatic418967fa.accept_7_6_3_4_1_294 55
  192 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 192 270 6 9 32 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 192 270
  (Polychromatic418967fa.accept_20_13_12_10_1_3619 53 192 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 192 270 2 26 96 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 51 192 270 3 17 64 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 192 270 2 25 96 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 192 270 (Polychromatic418967fa.accept_14_7_10_4_1_130
  49 192 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 192 270 6 8 32 45
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 192 270
  (Polychromatic418967fa.accept_17_13_5_15_1_8103 47 192 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 192 270 2 23 96 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 45 192 270 3 15 64 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 192 270 2 22 96 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 192 270 (Polychromatic418967fa.accept_7_1_3_4_1_128 43
  192 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 192 270 6 7 32 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 192 270
  (Polychromatic418967fa.accept_7_6_3_4_1_294 41 192 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 192 270 2 20 96 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 192 270 3 13 64 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 192 270 2 19 96 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 192 270 (Polychromatic418967fa.accept_19_18_2_4_1_7039 37 192
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 192 270 6 6 32 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 192 270
  (Polychromatic418967fa.accept_14_7_10_4_1_130 35 192 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 192 270 2 17 96 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 192 270 3 11 64 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 192 270 2 16 96 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 192 270 (Polychromatic418967fa.accept_19_12_2_4_1_9882 31 192
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 192 270 6 5 32 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 192 270
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 192 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 192 270 2 14 96 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 27 192 270 3 9 64 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 192 270 2 13 96 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 192 270 (Polychromatic418967fa.accept_19_6_2_4_1_9839 25 192 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 192 270 6 4 32 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 192 270
  (Polychromatic418967fa.accept_11_1_5_6_1_397 23 192 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 192 270 2 11 96 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 192 270 3 7 64 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 192 270 2 10 96 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 192 270 (Polychromatic418967fa.accept_21_19_3_18_1_7510 19 192 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 192 270 6 3 32 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 192 270
  (Polychromatic418967fa.accept_19_17_2_4_1_4278 17 192 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 192 270 2 8 96 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 192 270 3 5 64 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 192 270 2 7 96 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 192 270 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 192 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 192 270 6 2 32 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 192 270
  (Polychromatic418967fa.accept_17_11_5_15_1_8144 11 192 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 192 270 2 5 96 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 192 270 3 3 64 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 8 192 270 2 4 96 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 7 192 270 (Polychromatic418967fa.accept_14_7_10_4_1_130 7 192 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 192 270 6 1 32 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 192 270
  (Polychromatic418967fa.accept_19_5_2_4_1_9840 5 192 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 192 270 2 2 96 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 192 270 3 1 64 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 192 270 2 1 96 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 192 270 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 192 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 192
  270))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 191 270 (Eq.refl
  Bool.true) (allA_succ_of_accept 79 191 270 (accept_3_4 79 191 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 191 270 (Polychromatic418967fa.accept_17_10_4_15_1_2165 78 191 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 191 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 77
  191 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 191 270 (accept_3_4 76
  191 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 191 270
  (Polychromatic418967fa.accept_7_5_2_4_1_126 75 191 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 191 270 (Polychromatic418967fa.accept_16_10_15_14_1_1086 74 191 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 191 270 (accept_3_4 73 191 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 191 270 (Polychromatic418967fa.accept_14_2_9_4_1_1735 72 191 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 191 270
  (Polychromatic418967fa.accept_13_6_9_10_1_1201 71 191 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 191 270 (accept_3_4 70 191 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 191 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 191 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 191 270 (Polychromatic418967fa.accept_7_5_2_4_1_126 68 191 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 191 270 (accept_3_4 67 191 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 191 270 (Polychromatic418967fa.accept_13_1_9_10_1_625 66 191 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 191 270
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 191 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 191 270 (accept_3_4 64 191 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 191 270 (Polychromatic418967fa.accept_20_3_11_10_1_3545 63 191 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 191 270 (Polychromatic418967fa.accept_7_6_2_4_1_291 62 191 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 191 270 (accept_3_4 61 191 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 191 270 (Polychromatic418967fa.accept_19_3_1_4_1_1860 60 191 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 191 270
  (Polychromatic418967fa.accept_20_19_11_10_1_3615 59 191 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 191 270 (accept_3_4 58 191 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 191 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 191 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 191 270 (Polychromatic418967fa.accept_22_12_15_6_1_8826 56 191
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 191 270 (accept_3_4 55 191
  270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 191 270
  (Polychromatic418967fa.accept_7_5_2_4_1_126 54 191 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 191 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 191 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 191 270 (accept_3_4 52 191 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 191 270 (Polychromatic418967fa.accept_13_12_9_10_1_1223 51 191 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 191 270
  (Polychromatic418967fa.accept_17_16_4_15_1_4342 50 191 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 191 270 (accept_3_4 49 191 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 191 270 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 191 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 191 270 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 191 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 191 270 (accept_3_4 46 191 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 191 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 45
  191 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 191 270
  (Polychromatic418967fa.accept_14_2_9_4_1_1735 44 191 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 191 270 (accept_3_4 43 191 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 191 270 (Polychromatic418967fa.accept_16_10_15_14_1_1086 42 191 270 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 41 191 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 191 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 191 270 (accept_3_4 40 191 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 191 270 (Polychromatic418967fa.accept_16_7_15_14_1_2889 39 191
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 191 270
  (Polychromatic418967fa.accept_13_12_9_10_1_1223 38 191 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 191 270 (accept_3_4 37 191 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 191 270 (Polychromatic418967fa.accept_16_4_15_14_1_5056 36 191 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 191 270 (Polychromatic418967fa.accept_11_2_4_6_1_2412
  35 191 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 191 270 (accept_3_4 34
  191 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 191 270
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 191 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 191 270 (Polychromatic418967fa.accept_13_6_9_10_1_1201 32 191 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 191 270 (accept_3_4 31 191 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 191 270 (Polychromatic418967fa.accept_14_2_9_4_1_1735 30 191 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 191 270
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 191 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 191 270 (accept_3_4 28 191 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 191 270 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 191 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 191 270 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 191 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 191 270 (accept_3_4 25 191 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 191 270 (Polychromatic418967fa.accept_11_2_4_6_1_2412 24 191 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 191 270
  (Polychromatic418967fa.accept_16_7_15_14_1_2889 23 191 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 191 270 (accept_3_4 22 191 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 191 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 191 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 191 270 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 191 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 191 270 (accept_3_4 19 191 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 191 270
  (Polychromatic418967fa.accept_24_18_23_6_1_16562 18 191 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 191 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 191 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 191 270 (accept_3_4 16 191 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 191 270 (Polychromatic418967fa.accept_19_15_1_4_1_4238 15 191 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 191 270
  (Polychromatic418967fa.accept_13_1_9_10_1_625 14 191 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 191 270 (accept_3_4 13 191 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 191 270 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 191 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 191 270 (Polychromatic418967fa.accept_17_11_4_15_1_3150 11 191 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 191 270 (accept_3_4 10 191 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 191 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 191 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 191 270
  (Polychromatic418967fa.accept_22_8_15_6_1_8810 8 191 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 191 270 (accept_3_4 7 191 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  191 270 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 191 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 191 270 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 191 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 191 270 (accept_3_4 4 191 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 191 270 (Polychromatic418967fa.accept_19_3_1_4_1_1860 3 191 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 191 270
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 2 191 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 191 270 (accept_3_4 1 191 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 191
  270)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 81 190 270 (Eq.refl
  Bool.true) (allA_succ_of_gcd 80 190 270 10 8 19 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 190 270 (Polychromatic418967fa.accept_22_13_14_6_1_7111 79 190 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 190 270 2 39 95 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 190 270 (accept_3_5 77
  190 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 190 270 2 38 95 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 190 270 5 15 38 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 190 270 2 37 95 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 190 270
  (Polychromatic418967fa.accept_7_3_1_4_1_121 73 190 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 190 270 2 36 95 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 190 270 (accept_3_5 71 190 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 190 270 10 7 19 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 190 270 (Polychromatic418967fa.accept_12_9_10_6_1_872 69 190 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 190 270 2 34 95 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 190 270
  (Polychromatic418967fa.accept_13_2_8_10_1_1902 67 190 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 190 270 2 33 95 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 65 190 270 5 13 38 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 64 190 270 2 32 95 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 190 270 (Polychromatic418967fa.accept_11_8_3_6_1_1855 63 190
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 190 270 2 31 95 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 190 270
  (Polychromatic418967fa.accept_7_5_1_4_1_122 61 190 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 190 270 10 6 19 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 190 270 (accept_3_5 59 190 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 190 270 2 29 95 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 190 270 (Polychromatic418967fa.accept_12_9_10_6_1_872 57 190 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 190 270 2 28 95 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 190 270 5 11 38 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 190 270 2 27 95 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 190 270
  (accept_3_5 53 190 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 190 270 2 26 95 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 190 270
  (Polychromatic418967fa.accept_12_3_10_6_1_442 51 190 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 190 270 10 5 19 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 190 270 (Polychromatic418967fa.accept_24_1_22_6_1_11505 49 190 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 190 270 2 24 95 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 190 270 (accept_3_5 47 190 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 190 270 2 23 95 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 190 270 5 9 38 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 190 270 2 22 95 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 190 270
  (Polychromatic418967fa.accept_13_4_8_10_1_671 43 190 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 190 270 2 21 95 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 190 270 (accept_3_5 41 190 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 190 270 10 4 19 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 190 270 (Polychromatic418967fa.accept_12_3_10_6_1_442 39 190 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 190 270 2 19 95 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 190 270
  (Polychromatic418967fa.accept_13_11_8_10_1_676 37 190 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 190 270 2 18 95 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 35 190 270 5 7 38 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 34 190 270 2 17 95 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 190 270 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 190 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 190 270 2 16 95 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 190 270
  (Polychromatic418967fa.accept_7_3_1_4_1_121 31 190 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 190 270 10 3 19 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 190 270 (accept_3_5 29 190 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 190 270 2 14 95 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 190 270 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 190 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 190 270 2 13 95 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 190 270 5 5 38 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 190 270 2 12 95 135 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 190 270 (accept_3_5 23
  190 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 190 270 2 11 95 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 190 270
  (Polychromatic418967fa.accept_12_9_10_6_1_872 21 190 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 190 270 10 2 19 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 190 270 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 190 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 190 270 2 9 95 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 190 270 (accept_3_5 17 190 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 190 270 2 8 95 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 190 270 5 3 38 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 190 270 2 7 95 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 190 270
  (Polychromatic418967fa.accept_22_13_14_6_1_7111 13 190 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 190 270 2 6 95 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 190 270 (accept_3_5 11 190 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 190 270 10 1 19 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 190 270 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 190 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 190 270 2 4 95 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 190 270
  (Polychromatic418967fa.accept_13_7_8_10_1_2663 7 190 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 190 270 2 3 95 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 190 270 5 1 38 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 190 270 2 2 95 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 190 270 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 190 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 190 270 2 1 95 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 190 270 (Polychromatic418967fa.accept_17_1_3_15_1_2153
  1 190 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 190
  270))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 189 270 (Eq.refl
  Bool.true) (allA_succ_of_gcd 81 189 270 27 3 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 189 270 (Polychromatic418967fa.accept_12_8_9_6_1_127 80 189 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 189 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 79
  189 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 189 270 3 26 63 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 189 270
  (Polychromatic418967fa.accept_13_12_7_10_1_2662 77 189 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 189 270 (Polychromatic418967fa.accept_12_4_9_6_1_440 76 189 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 189 270 3 25 63 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 189 270
  (Polychromatic418967fa.accept_12_2_9_6_1_439 74 189 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 189 270 (Polychromatic418967fa.accept_13_8_7_10_1_4362 73 189 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 189 270 9 8 21 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 189 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 71
  189 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 189 270
  (Polychromatic418967fa.accept_11_4_2_6_1_389 70 189 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 189 270 3 23 63 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 189 270 (Polychromatic418967fa.accept_12_8_9_6_1_127 68 189 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 189 270 (Polychromatic418967fa.accept_4_3_1_2_1_62 67
  189 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 189 270 3 22 63 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 189 270
  (Polychromatic418967fa.accept_16_1_13_14_1_1064 65 189 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 189 270 (Polychromatic418967fa.accept_12_4_9_6_1_440 64 189 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 189 270 9 7 21 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 189 270
  (Polychromatic418967fa.accept_12_2_9_6_1_439 62 189 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 189 270 (Polychromatic418967fa.accept_17_10_2_15_1_3179 61 189 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 189 270 3 20 63 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 189 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 189 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 189 270 (Polychromatic418967fa.accept_12_10_9_6_1_1445 58 189 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 189 270 3 19 63 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 189 270 (Polychromatic418967fa.accept_12_8_9_6_1_127
  56 189 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 189 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 55 189 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 189 270 27 2 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 189 270 (Polychromatic418967fa.accept_14_11_7_4_1_3449 53 189 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 189 270 (Polychromatic418967fa.accept_12_4_9_6_1_440 52 189
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 189 270 3 17 63 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 189 270
  (Polychromatic418967fa.accept_12_2_9_6_1_439 50 189 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 189 270 (Polychromatic418967fa.accept_16_1_13_14_1_1064 49 189 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 189 270 3 16 63 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 189 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 189 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 189 270 (Polychromatic418967fa.accept_12_10_9_6_1_1445 46 189 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 189 270 9 5 21 30 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 189 270 (Polychromatic418967fa.accept_12_8_9_6_1_127
  44 189 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 189 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 189 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 189 270 3 14 63 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 189 270 (Polychromatic418967fa.accept_17_7_2_15_1_1255 41 189 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 189 270
  (Polychromatic418967fa.accept_12_4_9_6_1_440 40 189 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 189 270 3 13 63 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 189 270 (Polychromatic418967fa.accept_12_2_9_6_1_439 38 189 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 189 270 (Polychromatic418967fa.accept_11_4_2_6_1_389
  37 189 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 189 270 9 4 21 30
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 189 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 189 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 189 270 (Polychromatic418967fa.accept_12_10_9_6_1_1445 34 189 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 189 270 3 11 63 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 189 270 (Polychromatic418967fa.accept_12_8_9_6_1_127
  32 189 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 189 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 31 189 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 189 270 3 10 63 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 189 270 (Polychromatic418967fa.accept_13_3_7_10_1_668 29 189 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 189 270
  (Polychromatic418967fa.accept_12_4_9_6_1_440 28 189 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 189 270 27 1 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 189 270 (Polychromatic418967fa.accept_11_4_2_6_1_389 26 189 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 189 270 (Polychromatic418967fa.accept_13_12_7_10_1_2662 25 189
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 189 270 3 8 63 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 189 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 189 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 189 270 (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 189 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 189 270 3 7 63 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 189 270 (Polychromatic418967fa.accept_12_8_9_6_1_127
  20 189 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 189 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 189 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 189 270 9 2 21 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 189 270 (Polychromatic418967fa.accept_13_4_7_10_1_1200 17 189 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 189 270 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 189
  270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 189 270 3 5 63 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 189 270
  (Polychromatic418967fa.accept_12_2_9_6_1_439 14 189 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 189 270 (Polychromatic418967fa.accept_17_13_2_15_1_2151 13 189 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 189 270 3 4 63 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 189 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 189 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 189 270 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 189 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 189 270 9 1 21 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 189 270 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 189 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 189 270
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 189 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 189 270 3 2 63 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 189 270 (Polychromatic418967fa.accept_19_5_18_4_1_2956 5 189 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 189 270 (Polychromatic418967fa.accept_11_4_2_6_1_389 4 189 270
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 189 270 3 1 63 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 189 270
  (Polychromatic418967fa.accept_12_2_9_6_1_439 2 189 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 189 270 (Polychromatic418967fa.accept_16_1_13_14_1_1064 1 189 270 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 189
  270)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 188 270 (Eq.refl
  Bool.true) (allA_succ_of_gcd 82 188 270 2 41 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 188 270 (Polychromatic418967fa.accept_12_9_8_6_1_466 81 188 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 188 270 2 40 94 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 188 270 (accept_3_4 79 188 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 188 270 2 39 94 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 188 270
  (Polychromatic418967fa.accept_13_12_6_10_1_667 77 188 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 188 270 2 38 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 188 270 (Polychromatic418967fa.accept_7_5_6_4_1_117 75 188 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 188 270 2 37 94 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 188 270 (accept_3_4 73 188 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 188 270 2 36 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 188 270 (Polychromatic418967fa.accept_11_5_1_6_1_774
  71 188 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 188 270 2 35 94 135
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 188 270
  (Polychromatic418967fa.accept_12_9_8_6_1_466 69 188 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 188 270 2 34 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 188 270 (accept_3_4 67 188 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 188 270 2 33 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 188 270 (Polychromatic418967fa.accept_7_2_6_4_1_29 65 188 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 188 270 2 32 94 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 188 270
  (Polychromatic418967fa.accept_12_3_8_6_1_895 63 188 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 188 270 2 31 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 188 270 (accept_3_4 61 188 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 188 270 2 30 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 188 270 (Polychromatic418967fa.accept_7_3_6_4_1_30 59 188 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 188 270 2 29 94 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 188 270
  (Polychromatic418967fa.accept_12_9_8_6_1_466 57 188 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 188 270 2 28 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 188 270 (accept_3_4 55 188 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 188 270 2 27 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 188 270 (Polychromatic418967fa.accept_21_11_20_18_1_7656 53 188 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 188 270 2 26 94 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 188 270
  (Polychromatic418967fa.accept_7_2_6_4_1_29 51 188 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 188 270 2 25 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 188 270 (accept_3_4 49 188 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 188 270 2 24 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 188 270 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 188 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 188 270 2 23 94 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 188 270
  (Polychromatic418967fa.accept_7_3_6_4_1_30 45 188 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 188 270 2 22 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 188 270 (accept_3_4 43 188 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 188 270 2 21 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 188 270 (Polychromatic418967fa.accept_13_2_6_10_1_2703 41 188 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 188 270 2 20 94 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 188 270
  (Polychromatic418967fa.accept_12_3_8_6_1_895 39 188 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 188 270 2 19 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 188 270 (accept_3_4 37 188 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 188 270 2 18 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 188 270 (Polychromatic418967fa.accept_13_9_6_10_1_666 35 188 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 188 270 2 17 94 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 188 270
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 188 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 188 270 2 16 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 188 270 (accept_3_4 31 188 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 188 270 2 15 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 188 270 (Polychromatic418967fa.accept_11_7_1_6_1_1281 29 188 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 188 270 2 14 94 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 188 270
  (Polychromatic418967fa.accept_11_5_1_6_1_774 27 188 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 188 270 2 13 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 188 270 (accept_3_4 25 188 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 188 270 2 12 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 188 270 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 188 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 188 270 2 11 94 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 188 270
  (Polychromatic418967fa.accept_12_9_8_6_1_466 21 188 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 188 270 2 10 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 188 270 (accept_3_4 19 188 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 188 270 2 9 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 188 270 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 188 270 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 188 270 2 8 94 135 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 188 270
  (Polychromatic418967fa.accept_12_3_8_6_1_895 15 188 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 188 270 2 7 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 188 270 (accept_3_4 13 188 270 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 188 270 2 6 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 188 270 (Polychromatic418967fa.accept_19_11_17_4_1_11272 11 188 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 188 270 2 5 94 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 188 270
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 188 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 188 270 2 4 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 188 270 (accept_3_4 7 188 270 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 188
  270 2 3 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  188 270 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 188 270 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 188 270 2 2 94 135 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 188 270 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 188 270 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 188 270 2 1 94 135 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 188 270 (accept_3_4 1 188 270
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 188
  270)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_270_segment_002))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


