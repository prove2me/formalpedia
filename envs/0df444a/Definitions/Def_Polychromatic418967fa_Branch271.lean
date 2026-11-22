-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch271
-- name    : Polychromatic418967fa_Branch271
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:32:13.906485+00:00
-- url     : https://prove2.me/theorems/46345053-b4fe-488c-9fa4-334c4ca2c6fe
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch271_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_271 : allB 271 271 :=
  allB_succ' 2 270 271 (Eq.refl Bool.true) (allA_succ_of_accept 1 270 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 1
  270 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 270 271)) (allB_succ' 3 269 271
  (Eq.refl Bool.true) (allA_of_3_1 3 269 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 268 271 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 268 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 268 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 268 271 (accept_3_3 2 268 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 268 271 (Polychromatic418967fa.accept_13_1_8_11_1_724 1 268 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 268 271)))) (allB_succ' 5 267 271 (Eq.refl Bool.true)
  (allA_succ_of_accept 4 267 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 267 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 267 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 267 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 267 271 (accept_3_3 2 267 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 267 271 (Polychromatic418967fa.accept_13_1_7_11_1_702
  1 267 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 267 271))))) (allB_succ' 6 266 271
  (Eq.refl Bool.true) (allA_of_3_1 6 266 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 265 271 (Eq.refl
  Bool.true) (allA_succ_of_accept 6 265 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 265 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 265 271 (accept_3_3 5 265 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 265 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 265 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 265 271
  (Polychromatic418967fa.accept_9_3_4_1_1_22 3 265 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 265 271 (accept_3_3 2 265 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  265 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 265 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 265 271))))))) (allB_succ' 8 264 271 (Eq.refl Bool.true) (allA_succ_of_accept 7 264 271
  (Polychromatic418967fa.accept_9_7_3_1_1_386 7 264 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 264 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 264 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 264 271 (accept_3_3 5 264 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 264 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 264 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 264 271 (Polychromatic418967fa.accept_14_3_12_5_1_153
  3 264 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 264 271 (accept_3_3 2
  264 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 264 271
  (Polychromatic418967fa.accept_16_1_8_15_1_1945 1 264 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 264 271)))))))) (allB_succ' 9 263 271 (Eq.refl Bool.true) (allA_of_3_1 9 263 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 10 262 271 (Eq.refl Bool.true) (allA_succ_of_accept 9 262 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 262 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 262 271 (accept_3_3 8 262 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  262 271 (Polychromatic418967fa.accept_16_7_6_15_1_495 7 262 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 262 271 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 262 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 262 271 (accept_3_3 5 262 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 262 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 262 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 262 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 262 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 262 271 (accept_3_3 2 262 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  262 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 262 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 262 271)))))))))) (allB_succ' 11 261 271 (Eq.refl Bool.true) (allA_succ_of_accept 10 261 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 261 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 261 271 (Polychromatic418967fa.accept_13_9_1_11_1_275 9 261 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 261 271 (accept_3_3 8 261 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 261 271 (Polychromatic418967fa.accept_13_7_1_11_1_732 7 261 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 261 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 6
  261 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 261 271 (accept_3_3 5 261
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 261 271 (Polychromatic418967fa.accept_6_4_3_1_1_57
  4 261 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 261 271
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 261 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 261 271 (accept_3_3 2 261 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  261 271 (Polychromatic418967fa.accept_16_1_5_15_1_2918 1 261 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 261 271))))))))))) (allB_succ' 12 260 271 (Eq.refl Bool.true) (allA_of_3_1 12 260 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 259 271 (Eq.refl Bool.true) (allA_succ_of_accept 12 259 271
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 259 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 259 271 (accept_3_3 11 259 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 259 271 (Polychromatic418967fa.accept_13_10_12_11_1_731 10 259 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 259 271 (Polychromatic418967fa.accept_14_9_7_5_1_1105 9 259 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 259 271 (accept_3_3 8 259 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 259 271 (Polychromatic418967fa.accept_13_7_12_11_1_1911 7 259 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 259 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 259 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 259 271 (accept_3_3 5 259 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  259 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 259 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 259 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 259 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 259 271 (accept_3_3 2 259 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 259 271 (Polychromatic418967fa.accept_11_1_6_7_1_116 1 259 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 259 271))))))))))))) (allB_succ' 14 258 271 (Eq.refl
  Bool.true) (allA_succ_of_accept 13 258 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 258 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 258 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 12
  258 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 258 271 (accept_3_3 11
  258 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 258 271
  (Polychromatic418967fa.accept_19_10_11_5_1_7093 10 258 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 258 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 258 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 258 271 (accept_3_3 8 258 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 258 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 258 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 258 271
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 6 258 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 258 271 (accept_3_3 5 258 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  258 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 258 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 258 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 258 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 258 271 (accept_3_3 2 258 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 258 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 258 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 258 271)))))))))))))) (allB_succ' 15 257 271 (Eq.refl
  Bool.true) (allA_of_3_1 15 257 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 256 271 (Eq.refl Bool.true)
  (allA_succ_of_accept 15 256 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 256 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 256 271 (accept_3_3 14 256 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 256 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 256 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 256 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 12
  256 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 256 271 (accept_3_3 11
  256 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 256 271
  (Polychromatic418967fa.accept_11_10_3_7_1_2564 10 256 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 256 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 256 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 256 271 (accept_3_3 8 256 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 256 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 256 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 256 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 6
  256 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 256 271 (accept_3_3 5 256
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 256 271
  (Polychromatic418967fa.accept_11_4_3_7_1_828 4 256 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 256 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 256 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 256 271 (accept_3_3 2 256 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 256 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 256 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 256 271)))))))))))))))) (allB_succ' 17 255 271 (Eq.refl Bool.true)
  (allA_succ_of_accept 16 255 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 255 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 255 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 255 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 255 271 (accept_3_3 14 255 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 255 271 (Polychromatic418967fa.accept_9_4_3_1_1_154
  13 255 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 255 271
  (Polychromatic418967fa.accept_14_12_3_5_1_1868 12 255 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 255 271 (accept_3_3 11 255 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 255 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 255 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 255 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 255 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 255 271 (accept_3_3 8 255 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 255 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 255 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 255 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 255 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 255 271 (accept_3_3 5 255 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  255 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 255 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 255 271 (Polychromatic418967fa.accept_13_3_8_11_1_1906 3 255 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 255 271 (accept_3_3 2 255 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 255 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 255 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 255 271))))))))))))))))) (allB_succ' 18 254 271
  (Eq.refl Bool.true) (allA_of_3_1 18 254 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 253 271 (Eq.refl
  Bool.true) (allA_succ_of_accept 18 253 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 253 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 253 271 (accept_3_3 17 253 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 253 271 (Polychromatic418967fa.accept_21_16_1_19_1_10717 16 253 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 253 271
  (Polychromatic418967fa.accept_19_15_6_5_1_4356 15 253 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 253 271 (accept_3_3 14 253 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 253 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 253 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 253 271 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 253 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 253 271 (accept_3_3 11 253 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 253 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 253 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 253 271
  (Polychromatic418967fa.accept_27_9_10_1_1_5033 9 253 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 253 271 (accept_3_3 8 253 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  253 271 (Polychromatic418967fa.accept_19_7_6_5_1_4320 7 253 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 253 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 253 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 253 271 (accept_3_3 5 253 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 253 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 253 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 253 271
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 253 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 253 271 (accept_3_3 2 253 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  253 271 (Polychromatic418967fa.accept_17_1_15_16_1_2202 1 253 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 253 271))))))))))))))))))) (allB_succ' 20 252 271 (Eq.refl Bool.true) (allA_succ_of_accept 19
  252 271 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 252 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 252 271 (Polychromatic418967fa.accept_16_2_12_15_1_2908 18 252 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 252 271 (accept_3_3 17 252 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 252 271 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 252
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 252 271
  (Polychromatic418967fa.accept_17_15_14_16_1_5625 15 252 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 252 271 (accept_3_3 14 252 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 252 271 (Polychromatic418967fa.accept_10_3_2_1_1_839 13 252 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 252 271 (Polychromatic418967fa.accept_22_12_10_7_1_2604 12 252
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 252 271 (accept_3_3 11 252
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 252 271
  (Polychromatic418967fa.accept_27_10_9_1_1_14726 10 252 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 252 271 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 252 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 252 271 (accept_3_3 8 252 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 252 271 (Polychromatic418967fa.accept_13_7_5_11_1_1927 7 252 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 252 271
  (Polychromatic418967fa.accept_10_6_2_1_1_494 6 252 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 252 271 (accept_3_3 5 252 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  252 271 (Polychromatic418967fa.accept_15_4_12_1_1_1081 4 252 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 252 271 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 252 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 252 271 (accept_3_3 2 252 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 252 271 (Polychromatic418967fa.accept_20_1_12_11_1_3778 1 252 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 252 271)))))))))))))))))))) (allB_succ' 21 251 271
  (Eq.refl Bool.true) (allA_of_3_1 21 251 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 250 271 (Eq.refl
  Bool.true) (allA_succ_of_accept 21 250 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 250 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 250 271 (accept_3_3 20 250 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 250 271 (Polychromatic418967fa.accept_20_19_10_11_1_5107 19 250 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 250 271
  (Polychromatic418967fa.accept_13_5_3_11_1_1288 18 250 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 250 271 (accept_3_3 17 250 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 250 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 250 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 250 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 250 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 250 271 (accept_3_3 14 250 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 250 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 250 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 250 271
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 250 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 250 271 (accept_3_3 11 250 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 250 271 (Polychromatic418967fa.accept_13_10_3_11_1_1923 10 250 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 250 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 250 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 250 271 (accept_3_3 8 250 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 250 271 (Polychromatic418967fa.accept_13_7_3_11_1_280 7 250 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 250 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 250 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 250 271 (accept_3_3 5 250 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  250 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 250 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 250 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 250 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 250 271 (accept_3_3 2 250 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 250 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 250 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 250 271)))))))))))))))))))))) (allB_succ' 23 249 271
  (Eq.refl Bool.true) (allA_succ_of_accept 22 249 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 249 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 249 271
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 249 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 249 271 (accept_3_3 20 249 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 249 271 (Polychromatic418967fa.accept_27_19_6_1_1_3135 19 249 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 249 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 249 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 249 271 (accept_3_3 17 249 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 249 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 249 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 249 271
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 249 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 249 271 (accept_3_3 14 249 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 249 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 249 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 249 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 249 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 249 271 (accept_3_3 11 249 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 249 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 249 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 249 271
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 249 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 249 271 (accept_3_3 8 249 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  249 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 249 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 249 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 249 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 249 271 (accept_3_3 5 249 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 249 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 249 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 249 271
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 249 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 249 271 (accept_3_3 2 249 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  249 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 249 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 249 271))))))))))))))))))))))) (allB_succ' 24 248 271 (Eq.refl Bool.true) (allA_of_3_1 24 248
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 247 271 (Eq.refl Bool.true) (allA_succ_of_accept 24 247
  271 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 247 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 247 271 (accept_3_3 23 247 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 247 271 (Polychromatic418967fa.accept_16_6_7_15_1_1942 22 247 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 247 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 247 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 247 271 (accept_3_3 20 247 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 247 271
  (Polychromatic418967fa.accept_16_3_7_15_1_1130 19 247 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 247 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 247 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 247 271 (accept_3_3 17 247 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 247 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 247 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 247 271 (Polychromatic418967fa.accept_9_6_4_1_1_390
  15 247 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 247 271 (accept_3_3 14
  247 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 247 271
  (Polychromatic418967fa.accept_17_13_9_16_1_3254 13 247 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 247 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 247 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 247 271 (accept_3_3 11 247 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 247 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 247 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 247 271
  (Polychromatic418967fa.accept_11_9_5_7_1_815 9 247 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 247 271 (accept_3_3 8 247 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  247 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 247 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 247 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 247 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 247 271 (accept_3_3 5 247 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 247 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 247 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 247 271
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 247 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 247 271 (accept_3_3 2 247 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  247 271 (Polychromatic418967fa.accept_20_1_7_11_1_3673 1 247 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 247 271))))))))))))))))))))))))) (allB_succ' 26 246 271 (Eq.refl Bool.true) (allA_succ_of_accept
  25 246 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 246 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 246 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 246 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 246 271 (accept_3_3 23 246 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 246 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 246 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 246 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 246 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 246 271 (accept_3_3 20 246 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 246 271 (Polychromatic418967fa.accept_11_8_4_7_1_1303 19 246 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 246 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 246 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 246 271 (accept_3_3 17 246 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 246 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 246 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 246 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 246 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 246 271 (accept_3_3 14 246 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 246 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 246 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 246 271 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 246 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 246 271 (accept_3_3 11 246 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 246 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 246 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 246 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 246 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 246 271 (accept_3_3 8 246 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  246 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 246 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 246 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 246 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 246 271 (accept_3_3 5 246 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 246 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 246 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 246 271
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 246 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 246 271 (accept_3_3 2 246 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  246 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 246 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 246 271)))))))))))))))))))))))))) (allB_succ' 27 245 271 (Eq.refl Bool.true) (allA_of_3_1 27 245
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 244 271 (Eq.refl Bool.true) (allA_succ_of_accept 27 244
  271 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 244 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 244 271 (accept_3_3 26 244 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 244 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 244 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 244 271 (Polychromatic418967fa.accept_16_8_4_15_1_2941 24 244 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 244 271 (accept_3_3 23 244 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 244 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 244 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 244 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 244 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 244 271 (accept_3_3 20 244 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 244 271 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 244 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 244 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 244 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 244 271 (accept_3_3 17 244 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 244 271 (Polychromatic418967fa.accept_13_3_10_11_1_1293 16 244 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 244 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 244 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 244 271 (accept_3_3 14 244 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 244 271 (Polychromatic418967fa.accept_14_13_6_5_1_1853 13 244 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 244 271 (Polychromatic418967fa.accept_13_12_10_11_1_1279 12 244 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 244 271 (accept_3_3 11 244 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 244 271 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 244
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 244 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 244 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 244 271 (accept_3_3 8 244 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  244 271 (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 244 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 244 271 (Polychromatic418967fa.accept_21_6_13_19_1_4533 6 244 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 244 271 (accept_3_3 5 244 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 244 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 244 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 244 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 244 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 244 271 (accept_3_3 2 244 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  244 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 244 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 244 271)))))))))))))))))))))))))))) (allB_succ' 29 243 271 (Eq.refl Bool.true)
  (allA_succ_of_accept 28 243 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 243 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 243 271 (Polychromatic418967fa.accept_13_1_9_11_1_703 27 243
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 243 271 (accept_3_3 26 243
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 243 271
  (Polychromatic418967fa.accept_19_6_15_5_1_5697 25 243 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 243 271 (Polychromatic418967fa.accept_18_6_9_1_1_3769 24 243 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 243 271 (accept_3_3 23 243 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 243 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 243 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 243 271 (Polychromatic418967fa.accept_12_9_3_7_1_924
  21 243 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 243 271 (accept_3_3 20
  243 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 243 271
  (Polychromatic418967fa.accept_15_4_3_1_1_487 19 243 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 243 271 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 243 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 243 271 (accept_3_3 17 243 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 243 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 243 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 243 271 (Polychromatic418967fa.accept_13_2_9_11_1_258
  15 243 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 243 271 (accept_3_3 14
  243 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 243 271
  (Polychromatic418967fa.accept_15_13_3_1_1_3740 13 243 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 243 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 243 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 243 271 (accept_3_3 11 243 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 243 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 243 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 243 271 (Polychromatic418967fa.accept_12_9_3_7_1_924 9
  243 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 243 271 (accept_3_3 8 243
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 243 271
  (Polychromatic418967fa.accept_13_7_9_11_1_705 7 243 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 243 271 (Polychromatic418967fa.accept_11_6_1_7_1_1315 6 243 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 243 271 (accept_3_3 5 243 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 243 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 243 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 243 271 (Polychromatic418967fa.accept_18_3_9_1_1_3690
  3 243 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 243 271 (accept_3_3 2
  243 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 243 271
  (Polychromatic418967fa.accept_13_1_9_11_1_703 1 243 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 243 271))))))))))))))))))))))))))))) (allB_succ' 30 242 271 (Eq.refl Bool.true) (allA_of_3_1 30 242 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 241 271 (Eq.refl Bool.true) (allA_succ_of_accept 30 241 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 241 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 241 271 (accept_3_3 29 241 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 241 271 (Polychromatic418967fa.accept_19_9_13_5_1_4351 28 241 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 241 271 (Polychromatic418967fa.accept_13_1_7_11_1_702 27 241 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 241 271 (accept_3_3 26 241 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 241 271 (Polychromatic418967fa.accept_11_3_10_7_1_129 25 241
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 241 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 241 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 241 271 (accept_3_3 23 241 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 241 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 241 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 241 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 241 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 241 271 (accept_3_3 20 241 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 241 271 (Polychromatic418967fa.accept_22_19_21_7_1_11971 19 241 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 241 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 241 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 241 271 (accept_3_3 17 241 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 241 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 241 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 241 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 241 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 241 271 (accept_3_3 14 241 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 241 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 241 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 241 271
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 241 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 241 271 (accept_3_3 11 241 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 241 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 241 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 241 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 241 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 241 271 (accept_3_3 8 241 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 241 271 (Polychromatic418967fa.accept_17_7_3_16_1_2208 7 241 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 241 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 241 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 241 271 (accept_3_3 5 241 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  241 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 241 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 241 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 241 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 241 271 (accept_3_3 2 241 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 241 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 241 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 241 271))))))))))))))))))))))))))))))) (allB_succ' 32
  240 271 (Eq.refl Bool.true) (allA_succ_of_accept 31 240 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 240 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 240 271
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 240 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 240 271 (accept_3_3 29 240 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 240 271 (Polychromatic418967fa.accept_19_9_12_5_1_5695 28 240 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 240 271 (Polychromatic418967fa.accept_11_5_9_7_1_411 27 240 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 240 271 (accept_3_3 26 240 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 240 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 240 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 240 271
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 240 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 240 271 (accept_3_3 23 240 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 240 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 240 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 240 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 240 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 240 271 (accept_3_3 20 240 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 240 271 (Polychromatic418967fa.accept_25_19_15_21_1_16650 19 240 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 240 271
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 240 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 240 271 (accept_3_3 17 240 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 240 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 240 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 240 271 (Polychromatic418967fa.accept_19_15_12_5_1_8544 15 240 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 240 271 (accept_3_3 14 240 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 240 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 240 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 240 271
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 240 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 240 271 (accept_3_3 11 240 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 240 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 240 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 240 271 (Polychromatic418967fa.accept_18_9_6_1_1_3687 9 240 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 240 271 (accept_3_3 8 240 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 240 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 240 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 240 271
  (Polychromatic418967fa.accept_25_6_15_21_1_16649 6 240 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 240 271 (accept_3_3 5 240 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 240 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 240 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 240 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 240 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 240 271 (accept_3_3 2 240 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 240 271 (Polychromatic418967fa.accept_17_1_2_16_1_5596
  1 240 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 240
  271)))))))))))))))))))))))))))))))) (allB_succ' 33 239 271 (Eq.refl Bool.true) (allA_of_3_1 33 239 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 238 271 (Eq.refl Bool.true) (allA_succ_of_accept 33 238 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 238 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 238 271 (accept_3_3 32 238 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 238 271 (Polychromatic418967fa.accept_21_10_7_19_1_9208 31 238 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 238 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 238 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 238 271 (accept_3_3 29 238 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 238 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 238 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 238 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 238 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 238 271 (accept_3_3 26 238 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 238 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 238 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 238 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 238 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 238 271 (accept_3_3 23 238 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 238 271 (Polychromatic418967fa.accept_19_3_10_5_1_4314 22 238 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 238 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 238 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 238 271 (accept_3_3 20 238 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 238 271 (Polychromatic418967fa.accept_10_9_8_1_1_1331 19 238 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 238 271 (Polychromatic418967fa.accept_15_3_13_1_1_479 18 238 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 238 271 (accept_3_3 17 238 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 238 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 238 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 238 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 238 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 238 271 (accept_3_3 14 238 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 238 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 238 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 238 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 238 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 238 271 (accept_3_3 11 238 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 238 271 (Polychromatic418967fa.accept_13_10_4_11_1_1969 10 238 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 238 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 238 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 238 271 (accept_3_3 8 238 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  238 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 238 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 238 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 238 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 238 271 (accept_3_3 5 238 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 238 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 238 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 238 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 238 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 238 271 (accept_3_3 2 238 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  238 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 238 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 238 271)))))))))))))))))))))))))))))))))) (allB_succ' 35 237 271 (Eq.refl Bool.true)
  (allA_succ_of_accept 34 237 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 237 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 237 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 237 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 237 271 (accept_3_3 32 237 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 237 271 (Polychromatic418967fa.accept_9_4_3_1_1_154
  31 237 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 237 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 237 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 237 271 (accept_3_3 29 237 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 237 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 237 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 237 271 (Polychromatic418967fa.accept_12_3_9_7_1_472 27 237 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 237 271 (accept_3_3 26 237 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 237 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 237 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 237 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 237 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 237 271 (accept_3_3 23 237 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 237 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 237 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 237 271 (Polychromatic418967fa.accept_13_8_3_11_1_3467 21 237 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 237 271 (accept_3_3 20 237 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 237 271 (Polychromatic418967fa.accept_15_4_12_1_1_1081 19 237
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 237 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 237 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 237 271 (accept_3_3 17 237 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 237 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 237 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 237 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 237 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 237 271 (accept_3_3 14 237 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 237 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 237 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 237 271
  (Polychromatic418967fa.accept_11_1_6_7_1_116 12 237 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 237 271 (accept_3_3 11 237 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 237 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 237 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 237 271 (Polychromatic418967fa.accept_18_9_3_1_1_2559 9 237 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 237 271 (accept_3_3 8 237 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 237 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 237 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 237 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 237 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 237 271 (accept_3_3 5 237 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  237 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 237 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 237 271 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 237 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 237 271 (accept_3_3 2 237 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 237 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 237 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 237 271))))))))))))))))))))))))))))))))))) (allB_succ'
  36 236 271 (Eq.refl Bool.true) (allA_of_3_1 36 236 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 235 271
  (Eq.refl Bool.true) (allA_succ_of_accept 36 235 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 235 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 235 271 (accept_3_3 35 235 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 235 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 235 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 235 271
  (Polychromatic418967fa.accept_13_7_1_11_1_732 33 235 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 235 271 (accept_3_3 32 235 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 235 271 (Polychromatic418967fa.accept_19_12_7_5_1_5725 31 235 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 235 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 235 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 235 271 (accept_3_3 29 235 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 235 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 235 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 235 271
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 235 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 235 271 (accept_3_3 26 235 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 235 271 (Polychromatic418967fa.accept_11_3_4_7_1_114 25 235 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 235 271 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 235 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 235 271 (accept_3_3 23 235 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 235 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 235 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 235 271
  (Polychromatic418967fa.accept_13_8_1_11_1_1284 21 235 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 235 271 (accept_3_3 20 235 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 235 271 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 235 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 235 271 (Polychromatic418967fa.accept_21_18_4_19_1_1838 18 235 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 235 271 (accept_3_3 17 235 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 235 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 235 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 235 271
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 235 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 235 271 (accept_3_3 14 235 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 235 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 235 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 235 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 235 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 235 271 (accept_3_3 11 235 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 235 271 (Polychromatic418967fa.accept_13_10_1_11_1_1961 10 235 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 235 271
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 235 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 235 271 (accept_3_3 8 235 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  235 271 (Polychromatic418967fa.accept_13_7_1_11_1_732 7 235 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 235 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 235 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 235 271 (accept_3_3 5 235 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 235 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 235 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 235 271
  (Polychromatic418967fa.accept_11_3_4_7_1_114 3 235 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 235 271 (accept_3_3 2 235 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  235 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 235 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 235 271))))))))))))))))))))))))))))))))))))) (allB_succ' 38 234 271 (Eq.refl Bool.true)
  (allA_succ_of_accept 37 234 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 234 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 234 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 234 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 234 271 (accept_3_3 35 234 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 234 271
  (Polychromatic418967fa.accept_19_15_6_5_1_4356 34 234 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 234 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 234 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 234 271 (accept_3_3 32 234 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 234 271 (Polychromatic418967fa.accept_22_9_14_7_1_16648 31 234 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 234 271
  (Polychromatic418967fa.accept_7_2_3_5_1_34 30 234 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 234 271 (accept_3_3 29 234 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 234 271 (Polychromatic418967fa.accept_32_28_10_15_1_16647 28 234 271 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 234 271 (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 234 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 234 271 (accept_3_3 26 234 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 234 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 234 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 234 271
  (Polychromatic418967fa.accept_25_24_9_21_1_16646 24 234 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 234 271 (accept_3_3 23 234 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 234 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 234 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 234 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 234 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 234 271 (accept_3_3 20 234 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 234 271
  (Polychromatic418967fa.accept_22_19_14_7_1_16645 19 234 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 234 271 (Polychromatic418967fa.accept_19_18_6_5_1_4321 18 234 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 234 271 (accept_3_3 17 234 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 234 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 234 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 234 271
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 234 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 234 271 (accept_3_3 14 234 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 234 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 234 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 234 271 (Polychromatic418967fa.accept_14_12_10_5_1_2712 12 234 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 234 271 (accept_3_3 11 234 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 234 271 (Polychromatic418967fa.accept_11_10_3_7_1_2564 10 234
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 234 271
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 234 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 234 271 (accept_3_3 8 234 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  234 271 (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 234 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 234 271 (Polychromatic418967fa.accept_15_6_9_1_1_1823 6 234 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 234 271 (accept_3_3 5 234 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 234 271 (Polychromatic418967fa.accept_11_4_3_7_1_828 4 234 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 234 271
  (Polychromatic418967fa.accept_17_3_13_16_1_2183 3 234 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 234 271 (accept_3_3 2 234 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  234 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 234 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 234 271)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 233 271 (Eq.refl Bool.true)
  (allA_of_3_1 39 233 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 40 232 271 (Eq.refl Bool.true)
  (allA_succ_of_accept 39 232 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 232 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 232 271 (accept_3_3 38 232 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 232 271 (Polychromatic418967fa.accept_19_18_4_5_1_5723 37 232 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 232 271
  (Polychromatic418967fa.accept_10_6_2_1_1_494 36 232 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 232 271 (accept_3_3 35 232 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 232 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 232 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 232 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 232 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 232 271 (accept_3_3 32 232 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 232 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 232 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 232 271
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 232 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 232 271 (accept_3_3 29 232 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 232 271 (Polychromatic418967fa.accept_11_6_1_7_1_1315 28 232 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 232 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 232 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 232 271 (accept_3_3 26 232 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 232 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 232 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 232 271
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 232 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 232 271 (accept_3_3 23 232 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 232 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 232 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 232 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 232 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 232 271 (accept_3_3 20 232 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 232 271 (Polychromatic418967fa.accept_10_9_2_1_1_840 19 232 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 232 271
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 232 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 232 271 (accept_3_3 17 232 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 232 271 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 232 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 232 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 232 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 232 271 (accept_3_3 14 232 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 232 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 232 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 232 271
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 232 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 232 271 (accept_3_3 11 232 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 232 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 232 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 232 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 232 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 232 271 (accept_3_3 8 232 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 232 271 (Polychromatic418967fa.accept_16_7_8_15_1_6327 7 232 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 232 271
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 232 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 232 271 (accept_3_3 5 232 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  232 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 232 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 232 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 232 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 232 271 (accept_3_3 2 232 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 232 271 (Polychromatic418967fa.accept_16_1_8_15_1_1945 1 232 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 232 271))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 41 231 271 (Eq.refl Bool.true) (allA_succ_of_accept 40 231 271 (Polychromatic418967fa.accept_6_4_3_1_1_57
  40 231 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 231 271
  (Polychromatic418967fa.accept_9_3_6_1_1_24 39 231 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 231 271 (accept_3_3 38 231 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 231 271 (Polychromatic418967fa.accept_14_9_7_5_1_1105 37 231 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 231 271 (Polychromatic418967fa.accept_19_17_3_5_1_3088 36 231 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 231 271 (accept_3_3 35 231 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 231 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 231 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 231 271
  (Polychromatic418967fa.accept_12_9_3_7_1_924 33 231 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 231 271 (accept_3_3 32 231 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 231 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 231 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 231 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 231 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 231 271 (accept_3_3 29 231 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 231 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 231 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 231 271
  (Polychromatic418967fa.accept_13_1_10_11_1_1280 27 231 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 231 271 (accept_3_3 26 231 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 231 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 231 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 231 271 (Polychromatic418967fa.accept_15_9_6_1_1_493 24 231
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 231 271 (accept_3_3 23 231
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 231 271
  (Polychromatic418967fa.accept_6_4_3_1_1_57 22 231 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 231 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 231 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 231 271 (accept_3_3 20 231 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 231 271 (Polychromatic418967fa.accept_16_3_7_15_1_1130 19 231 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 231 271
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 18 231 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 231 271 (accept_3_3 17 231 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 231 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 231 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 231 271 (Polychromatic418967fa.accept_13_2_10_11_1_1276 15 231 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 231 271 (accept_3_3 14 231 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 231 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 231 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 231 271
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 231 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 231 271 (accept_3_3 11 231 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 231 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 231 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 231 271 (Polychromatic418967fa.accept_12_9_3_7_1_924 9 231 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 231 271 (accept_3_3 8 231 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 231 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 231 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 231 271
  (Polychromatic418967fa.accept_16_6_7_15_1_1942 6 231 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 231 271 (accept_3_3 5 231 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  231 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 231 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 231 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 231 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 231 271 (accept_3_3 2 231 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 231 271 (Polychromatic418967fa.accept_13_1_10_11_1_1280 1 231 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 231 271)))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 42 230 271 (Eq.refl Bool.true) (allA_of_3_1 42 230 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 43 229 271 (Eq.refl Bool.true) (allA_succ_of_accept 42 229 271 (Polychromatic418967fa.accept_4_2_1_3_1_27
  42 229 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 229 271 (accept_3_3 41
  229 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 229 271
  (Polychromatic418967fa.accept_13_1_8_11_1_724 40 229 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 229 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 229 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 229 271 (accept_3_3 38 229 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 229 271 (Polychromatic418967fa.accept_19_18_1_5_1_5720 37 229 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 229 271
  (Polychromatic418967fa.accept_13_10_8_11_1_1985 36 229 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 229 271 (accept_3_3 35 229 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 229 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 229 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 229 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 229 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 229 271 (accept_3_3 32 229 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 229 271
  (Polychromatic418967fa.accept_17_14_8_16_1_6863 31 229 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 229 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 229 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 229 271 (accept_3_3 29 229 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 229 271 (Polychromatic418967fa.accept_10_8_9_1_1_189 28 229 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 229 271
  (Polychromatic418967fa.accept_11_5_9_7_1_411 27 229 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 229 271 (accept_3_3 26 229 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 229 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 229 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 229 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 229 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 229 271 (accept_3_3 23 229 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 229 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 229 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 229 271
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 229 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 229 271 (accept_3_3 20 229 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 229 271 (Polychromatic418967fa.accept_13_6_8_11_1_5398 19 229 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 229 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 229 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 229 271 (accept_3_3 17 229 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 229 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 229 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 229 271
  (Polychromatic418967fa.accept_9_6_4_1_1_390 15 229 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 229 271 (accept_3_3 14 229 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 229 271 (Polychromatic418967fa.accept_11_2_9_7_1_124 13 229 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 229 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 229 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 229 271 (accept_3_3 11 229 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 229 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 229 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 229 271
  (Polychromatic418967fa.accept_13_9_8_11_1_725 9 229 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 229 271 (accept_3_3 8 229 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  229 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 229 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 229 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 229 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 229 271 (accept_3_3 5 229 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 229 271 (Polychromatic418967fa.accept_13_4_8_11_1_1937 4 229 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 229 271
  (Polychromatic418967fa.accept_9_3_4_1_1_22 3 229 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 229 271 (accept_3_3 2 229 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  229 271 (Polychromatic418967fa.accept_13_1_8_11_1_724 1 229 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 229 271))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 228 271 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 228 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 228 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 228 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 228 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 228 271 (accept_3_3 41 228 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 228 271 (Polychromatic418967fa.accept_9_4_3_1_1_154
  40 228 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 228 271
  (Polychromatic418967fa.accept_10_9_8_1_1_1331 39 228 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 228 271 (accept_3_3 38 228 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 228 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 228 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 228 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 228 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 228 271 (accept_3_3 35 228 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 228 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 228 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 228 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 33 228 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 228 271 (accept_3_3 32 228 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 228 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 228 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 228 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 228 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 228 271 (accept_3_3 29 228 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 228 271 (Polychromatic418967fa.accept_15_13_3_1_1_3740 28 228 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 228 271
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 228 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 228 271 (accept_3_3 26 228 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 228 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 228 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 228 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 228 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 228 271 (accept_3_3 23 228 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 228 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 228 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 228 271
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 21 228 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 228 271 (accept_3_3 20 228 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 228 271 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 228 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 228 271 (Polychromatic418967fa.accept_13_5_7_11_1_3470 18 228 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 228 271 (accept_3_3 17 228 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 228 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 228 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 228 271
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 228 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 228 271 (accept_3_3 14 228 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 228 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 228 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 228 271 (Polychromatic418967fa.accept_13_12_7_11_1_1935 12 228 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 228 271 (accept_3_3 11 228 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 228 271 (Polychromatic418967fa.accept_17_10_7_16_1_6841 10 228
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 228 271
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 228 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 228 271 (accept_3_3 8 228 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  228 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 228 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 228 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 228 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 228 271 (accept_3_3 5 228 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 228 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 228 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 228 271
  (Polychromatic418967fa.accept_8_3_4_7_1_475 3 228 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 228 271 (accept_3_3 2 228 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  228 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 228 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 228 271)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 227 271 (Eq.refl Bool.true)
  (allA_of_3_1 45 227 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 46 226 271 (Eq.refl Bool.true)
  (allA_succ_of_accept 45 226 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 226 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 226 271 (accept_3_3 44 226 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 226 271 (Polychromatic418967fa.accept_21_1_16_19_1_3134 43 226 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 226 271
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 226 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 226 271 (accept_3_3 41 226 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 226 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 226 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 226 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 226 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 226 271 (accept_3_3 38 226 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 226 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 226 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 226 271
  (Polychromatic418967fa.accept_17_2_5_16_1_1264 36 226 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 226 271 (accept_3_3 35 226 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 226 271 (Polychromatic418967fa.accept_11_1_6_7_1_116 34 226 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 226 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 226 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 226 271 (accept_3_3 32 226 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 226 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 226 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 226 271
  (Polychromatic418967fa.accept_19_11_17_5_1_8609 30 226 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 226 271 (accept_3_3 29 226 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 226 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 226 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 226 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 226 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 226 271 (accept_3_3 26 226 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 226 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 25
  226 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 226 271
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 226 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 226 271 (accept_3_3 23 226 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 226 271 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 226 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 226 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 226 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 226 271 (accept_3_3 20 226 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 226 271 (Polychromatic418967fa.accept_13_6_5_11_1_1971 19 226 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 226 271
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 226 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 226 271 (accept_3_3 17 226 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 226 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 226 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 226 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 226 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 226 271 (accept_3_3 14 226 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 226 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 226 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 226 271
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 226 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 226 271 (accept_3_3 11 226 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 226 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 226 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 226 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 226 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 226 271 (accept_3_3 8 226 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 226 271 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 226 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 226 271
  (Polychromatic418967fa.accept_13_6_5_11_1_1971 6 226 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 226 271 (accept_3_3 5 226 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  226 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 226 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 226 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 226 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 226 271 (accept_3_3 2 226 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 226 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 226 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 226 271))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 47 225 271 (Eq.refl Bool.true) (allA_succ_of_accept 46 225 271 (Polychromatic418967fa.accept_4_2_1_3_1_27
  46 225 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 225 271
  (Polychromatic418967fa.accept_7_3_1_5_1_44 45 225 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 225 271 (accept_3_3 44 225 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 225 271 (Polychromatic418967fa.accept_16_11_1_15_1_1123 43 225 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 225 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 225 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 225 271 (accept_3_3 41 225 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 225 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 225 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 225 271
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 225 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 225 271 (accept_3_3 38 225 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 225 271 (Polychromatic418967fa.accept_16_5_1_15_1_3922 37 225 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 225 271 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 225 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 225 271 (accept_3_3 35 225 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 225 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 225 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 225 271
  (Polychromatic418967fa.accept_13_7_4_11_1_1967 33 225 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 225 271 (accept_3_3 32 225 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 225 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 225 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 225 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 225 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 225 271 (accept_3_3 29 225 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 225 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 225 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 225 271
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 225 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 225 271 (accept_3_3 26 225 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 225 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 225 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 225 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 225 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 225 271 (accept_3_3 23 225 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 225 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 225 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 225 271
  (Polychromatic418967fa.accept_13_8_4_11_1_3469 21 225 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 225 271 (accept_3_3 20 225 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 225 271 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 225 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 225 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 225 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 225 271 (accept_3_3 17 225 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 225 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 225 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 225 271
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 225 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 225 271 (accept_3_3 14 225 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 225 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 225 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 225 271 (Polychromatic418967fa.accept_13_12_4_11_1_1925 12 225 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 225 271 (accept_3_3 11 225 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 225 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 225 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 225 271
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 225 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 225 271 (accept_3_3 8 225 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  225 271 (Polychromatic418967fa.accept_13_7_4_11_1_1967 7 225 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 225 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 225 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 225 271 (accept_3_3 5 225 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 225 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 225 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 225 271
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 225 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 225 271 (accept_3_3 2 225 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  225 271 (Polychromatic418967fa.accept_19_1_16_5_1_5671 1 225 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 225 271))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 224 271 (Eq.refl
  Bool.true) (allA_of_3_1 48 224 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 223 271 (Eq.refl Bool.true)
  (allA_succ_of_accept 48 223 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 48 223 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 223 271 (accept_3_3 47 223 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 223 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 223 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 223 271
  (Polychromatic418967fa.accept_25_20_23_21_1_7825 45 223 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 223 271 (accept_3_3 44 223 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 223 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 223 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 223 271 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 223 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 223 271 (accept_3_3 41 223 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 223 271 (Polychromatic418967fa.accept_9_4_7_1_1_379
  40 223 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 223 271
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 223 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 223 271 (accept_3_3 38 223 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 223 271 (Polychromatic418967fa.accept_11_4_3_7_1_828 37 223 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 223 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 223 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 223 271 (accept_3_3 35 223 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 223 271 (Polychromatic418967fa.accept_14_6_13_5_1_534 34 223 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 223 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 33 223 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 223 271 (accept_3_3 32 223 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 223 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 223 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 223 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 223 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 223 271 (accept_3_3 29 223 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 223 271 (Polychromatic418967fa.accept_10_8_3_1_1_1316 28 223 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 223 271
  (Polychromatic418967fa.accept_15_12_13_1_1_3695 27 223 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 223 271 (accept_3_3 26 223 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 223 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 223 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 223 271 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 223 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 223 271 (accept_3_3 23 223 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 223 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 22
  223 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 223 271
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 223 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 223 271 (accept_3_3 20 223 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 223 271 (Polychromatic418967fa.accept_22_19_3_7_1_5501 19 223 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 223 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 223 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 223 271 (accept_3_3 17 223 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 223 271 (Polychromatic418967fa.accept_13_3_2_11_1_1999 16 223 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 223 271
  (Polychromatic418967fa.accept_7_1_6_5_1_39 15 223 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 223 271 (accept_3_3 14 223 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 223 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 223 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 223 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 223 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 223 271 (accept_3_3 11 223 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 223 271 (Polychromatic418967fa.accept_11_10_3_7_1_2564 10 223 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 223 271
  (Polychromatic418967fa.accept_13_9_2_11_1_1964 9 223 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 223 271 (accept_3_3 8 223 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  223 271 (Polychromatic418967fa.accept_21_7_13_19_1_4477 7 223 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 223 271 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 223 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 223 271 (accept_3_3 5 223 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 223 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 223 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 223 271
  (Polychromatic418967fa.accept_9_3_7_1_1_143 3 223 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 223 271 (accept_3_3 2 223 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  223 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 223 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 223 271))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 222 271 (Eq.refl
  Bool.true) (allA_succ_of_accept 49 222 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 222 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 222 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 48
  222 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 222 271 (accept_3_3 47
  222 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 222 271
  (Polychromatic418967fa.accept_10_6_2_1_1_494 46 222 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 222 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 222 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 222 271 (accept_3_3 44 222 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 222 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 222 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 222 271 (Polychromatic418967fa.accept_11_9_2_7_1_1298
  42 222 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 222 271 (accept_3_3 41
  222 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 222 271
  (Polychromatic418967fa.accept_9_4_6_1_1_393 40 222 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 222 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 222 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 222 271 (accept_3_3 38 222 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 222 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 222 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 222 271 (Polychromatic418967fa.accept_10_6_2_1_1_494
  36 222 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 222 271 (accept_3_3 35
  222 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 222 271
  (Polychromatic418967fa.accept_9_7_6_1_1_709 34 222 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 222 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 222 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 222 271 (accept_3_3 32 222 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 222 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 222 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 222 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 30
  222 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 222 271 (accept_3_3 29
  222 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 222 271
  (Polychromatic418967fa.accept_15_13_12_1_1_1841 28 222 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 222 271 (Polychromatic418967fa.accept_18_9_6_1_1_3687 27 222 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 222 271 (accept_3_3 26 222 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 222 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 222 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 222 271
  (Polychromatic418967fa.accept_14_10_12_5_1_3466 24 222 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 222 271 (accept_3_3 23 222 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 222 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 222 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 222 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 222 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 222 271 (accept_3_3 20 222 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 222 271 (Polychromatic418967fa.accept_10_9_2_1_1_840
  19 222 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 222 271
  (Polychromatic418967fa.accept_19_18_13_5_1_8608 18 222 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 222 271 (accept_3_3 17 222 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 222 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 222 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 222 271 (Polychromatic418967fa.accept_17_15_1_16_1_8166 15 222
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 222 271 (accept_3_3 14 222
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 222 271 (Polychromatic418967fa.accept_4_1_2_3_1_9
  13 222 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 222 271
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 222 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 222 271 (accept_3_3 11 222 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 222 271 (Polychromatic418967fa.accept_13_10_1_11_1_1961 10 222 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 222 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 222 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 222 271 (accept_3_3 8 222 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 222 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 222 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 222 271
  (Polychromatic418967fa.accept_10_6_2_1_1_494 6 222 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 222 271 (accept_3_3 5 222 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  222 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 222 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 222 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 222 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 222 271 (accept_3_3 2 222 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 222 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 222 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 222
  271)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 221 271 (Eq.refl Bool.true) (allA_of_3_1 51 221
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 220 271 (Eq.refl Bool.true) (allA_succ_of_accept 51 220
  271 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 220 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 220 271 (accept_3_3 50 220 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 220 271 (Polychromatic418967fa.accept_13_10_12_11_1_731 49 220 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 220 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 220 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 220 271 (accept_3_3 47 220 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 220 271 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 220 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 220 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 220 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 220 271 (accept_3_3 44 220 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 220 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 220 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 220 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 220 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 220 271 (accept_3_3 41 220 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 220 271 (Polychromatic418967fa.accept_13_1_12_11_1_728 40 220 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 220 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 220 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 220 271 (accept_3_3 38 220 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 220 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 220 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 220 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 220 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 220 271 (accept_3_3 35 220 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 220 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 220 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 220 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 220 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 220 271 (accept_3_3 32 220 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 220 271 (Polychromatic418967fa.accept_19_12_11_5_1_950 31 220 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 220 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 220 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 220 271 (accept_3_3 29 220 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 220 271 (Polychromatic418967fa.accept_15_13_10_1_1_1862 28 220 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 220 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 220 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 220 271 (accept_3_3 26 220 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 220 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 220 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 220 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 220 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 220 271 (accept_3_3 23 220 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 220 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 220 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 220 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 220 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 220 271 (accept_3_3 20 220 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 220 271 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 220 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 220 271 (Polychromatic418967fa.accept_16_2_12_15_1_2908 18 220 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 220 271 (accept_3_3 17 220 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 220 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 220 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 220 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 220 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 220 271 (accept_3_3 14 220 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 220 271 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 220 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 220 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 220 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 220 271 (accept_3_3 11 220 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 220 271 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 220 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 220 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 220 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 220 271 (accept_3_3 8 220 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  220 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 220 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 220 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 220 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 220 271 (accept_3_3 5 220 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 220 271 (Polychromatic418967fa.accept_13_4_12_11_1_5362 4 220 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 220 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 220 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 220 271 (accept_3_3 2 220 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  220 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 220 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 220 271)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 219 271 (Eq.refl
  Bool.true) (allA_succ_of_accept 52 219 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 219 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 219 271 (Polychromatic418967fa.accept_9_6_3_1_1_155
  51 219 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 219 271 (accept_3_3 50
  219 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 219 271
  (Polychromatic418967fa.accept_9_4_3_1_1_154 49 219 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 219 271 (Polychromatic418967fa.accept_10_8_9_1_1_189 48 219 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 219 271 (accept_3_3 47 219 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 219 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 219 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 219 271 (Polychromatic418967fa.accept_7_3_2_5_1_147
  45 219 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 219 271 (accept_3_3 44
  219 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 219 271
  (Polychromatic418967fa.accept_9_7_3_1_1_386 43 219 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 219 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 219 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 219 271 (accept_3_3 41 219 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 219 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 219 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 219 271 (Polychromatic418967fa.accept_7_4_2_5_1_527
  39 219 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 219 271 (accept_3_3 38
  219 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 219 271
  (Polychromatic418967fa.accept_15_7_9_1_1_473 37 219 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 219 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 219 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 219 271 (accept_3_3 35 219 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 219 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 219 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 219 271 (Polychromatic418967fa.accept_9_6_3_1_1_155
  33 219 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 219 271 (accept_3_3 32
  219 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 219 271
  (Polychromatic418967fa.accept_7_3_2_5_1_147 31 219 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 219 271 (Polychromatic418967fa.accept_18_12_3_1_1_3685 30 219 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 219 271 (accept_3_3 29 219 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 219 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 219 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 219 271 (Polychromatic418967fa.accept_18_9_3_1_1_2559
  27 219 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 219 271 (accept_3_3 26
  219 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 219 271
  (Polychromatic418967fa.accept_7_4_2_5_1_527 25 219 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 219 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 219 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 219 271 (accept_3_3 23 219 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 219 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 219 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 219 271 (Polychromatic418967fa.accept_12_9_3_7_1_924
  21 219 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 219 271 (accept_3_3 20
  219 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 219 271
  (Polychromatic418967fa.accept_16_3_11_15_1_1963 19 219 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 219 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 219 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 219 271 (accept_3_3 17 219 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 219 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 219 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 219 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 219 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 219 271 (accept_3_3 14 219 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 219 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 219 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 219 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 219 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 219 271 (accept_3_3 11 219 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 219 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 219 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 219 271
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 219 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 219 271 (accept_3_3 8 219 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  219 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 219 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 219 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 219 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 219 271 (accept_3_3 5 219 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 219 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 219 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 219 271
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 219 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 219 271 (accept_3_3 2 219 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  219 271 (Polychromatic418967fa.accept_16_1_11_15_1_498 1 219 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 219 271))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 218 271 (Eq.refl
  Bool.true) (allA_of_3_1 54 218 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 217 271 (Eq.refl Bool.true)
  (allA_succ_of_accept 54 217 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 217 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 217 271 (accept_3_3 53 217 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 217 271 (Polychromatic418967fa.accept_19_14_8_5_1_8606 52 217 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 217 271
  (Polychromatic418967fa.accept_14_9_7_5_1_1105 51 217 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 217 271 (accept_3_3 50 217 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 217 271 (Polychromatic418967fa.accept_23_3_10_18_1_16644 49 217 271 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 217 271 (Polychromatic418967fa.accept_11_4_8_7_1_819 48 217 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 217 271 (accept_3_3 47 217 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 217 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 217 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 217 271
  (Polychromatic418967fa.accept_20_5_17_11_1_6571 45 217 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 217 271 (accept_3_3 44 217 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 217 271 (Polychromatic418967fa.accept_17_9_13_16_1_3266 43 217 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 217 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 42
  217 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 217 271 (accept_3_3 41
  217 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 217 271
  (Polychromatic418967fa.accept_13_1_9_11_1_703 40 217 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 217 271 (Polychromatic418967fa.accept_15_9_7_1_1_1075 39 217 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 217 271 (accept_3_3 38 217 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 217 271 (Polychromatic418967fa.accept_11_4_8_7_1_819 37 217 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 217 271
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 217 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 217 271 (accept_3_3 35 217 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 217 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 217 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 217 271 (Polychromatic418967fa.accept_13_7_9_11_1_705 33 217 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 217 271 (accept_3_3 32 217 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 217 271 (Polychromatic418967fa.accept_19_12_8_5_1_8538 31 217
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 217 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 217 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 217 271 (accept_3_3 29 217 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 217 271 (Polychromatic418967fa.accept_13_2_9_11_1_258 28 217 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 217 271 (Polychromatic418967fa.accept_13_1_9_11_1_703 27 217 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 217 271 (accept_3_3 26 217 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 217 271 (Polychromatic418967fa.accept_15_10_7_1_1_3686 25 217
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 217 271
  (Polychromatic418967fa.accept_10_4_7_1_1_471 24 217 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 217 271 (accept_3_3 23 217 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 217 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 217 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 217 271 (Polychromatic418967fa.accept_13_8_9_11_1_1265 21 217 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 217 271 (accept_3_3 20 217 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 217 271 (Polychromatic418967fa.accept_24_19_1_7_1_9846 19 217
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 217 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 217 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 217 271 (accept_3_3 17 217 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 217 271 (Polychromatic418967fa.accept_10_6_7_1_1_1297 16 217 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 217 271 (Polychromatic418967fa.accept_11_4_8_7_1_819 15 217 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 217 271 (accept_3_3 14 217 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 217 271 (Polychromatic418967fa.accept_19_13_8_5_1_8539 13 217
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 217 271
  (Polychromatic418967fa.accept_14_12_7_5_1_1107 12 217 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 217 271 (accept_3_3 11 217 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 217 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 217 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 217 271 (Polychromatic418967fa.accept_14_9_7_5_1_1105 9 217 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 217 271 (accept_3_3 8 217 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 217 271 (Polychromatic418967fa.accept_13_7_9_11_1_705 7 217 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 217 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 217 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 217 271 (accept_3_3 5 217 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  217 271 (Polychromatic418967fa.accept_10_4_7_1_1_471 4 217 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 217 271 (Polychromatic418967fa.accept_17_3_13_16_1_2183 3 217 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 217 271 (accept_3_3 2 217 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 217 271 (Polychromatic418967fa.accept_13_1_9_11_1_703 1 217 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 217
  271))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 216 271 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 216 271 (Polychromatic418967fa.accept_10_5_6_1_1_836 55 216 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 216 271 (Polychromatic418967fa.accept_15_9_6_1_1_493 54 216
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 216 271 (accept_3_3 53 216
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 216 271
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 52 216 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 216 271 (Polychromatic418967fa.accept_19_13_7_5_1_5712 51 216 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 216 271 (accept_3_3 50 216 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 216 271 (Polychromatic418967fa.accept_13_10_8_11_1_1985 49 216 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 216 271
  (Polychromatic418967fa.accept_13_9_8_11_1_725 48 216 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 216 271 (accept_3_3 47 216 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 216 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 216 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 216 271 (Polychromatic418967fa.accept_10_5_6_1_1_836 45 216 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 216 271 (accept_3_3 44 216 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 216 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 216 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 216 271
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 216 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 216 271 (accept_3_3 41 216 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 216 271 (Polychromatic418967fa.accept_13_1_8_11_1_724 40 216 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 216 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 216 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 216 271 (accept_3_3 38 216 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 216 271 (Polychromatic418967fa.accept_10_7_6_1_1_486 37 216 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 216 271
  (Polychromatic418967fa.accept_7_1_6_5_1_39 36 216 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 216 271 (accept_3_3 35 216 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 216 271 (Polychromatic418967fa.accept_21_13_6_19_1_4489 34 216 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 216 271 (Polychromatic418967fa.accept_15_3_6_1_1_1834 33 216 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 216 271 (accept_3_3 32 216 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 216 271 (Polychromatic418967fa.accept_19_12_7_5_1_5725 31 216
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 216 271
  (Polychromatic418967fa.accept_13_4_8_11_1_1937 30 216 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 216 271 (accept_3_3 29 216 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 216 271 (Polychromatic418967fa.accept_16_12_8_15_1_5119 28 216 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 216 271 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 216 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 216 271 (accept_3_3 26 216 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 216 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 216 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 216 271
  (Polychromatic418967fa.accept_15_9_6_1_1_493 24 216 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 216 271 (accept_3_3 23 216 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 216 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 216 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 216 271 (Polychromatic418967fa.accept_19_2_7_5_1_3067 21 216 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 216 271 (accept_3_3 20 216 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 216 271 (Polychromatic418967fa.accept_13_6_8_11_1_5398 19 216
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 216 271
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 216 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 216 271 (accept_3_3 17 216 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 216 271 (Polychromatic418967fa.accept_13_3_8_11_1_1906 16 216 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 216 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 216 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 216 271 (accept_3_3 14 216 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 216 271 (Polychromatic418967fa.accept_14_13_6_5_1_1853 13 216 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 216 271
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 216 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 216 271 (accept_3_3 11 216 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 216 271 (Polychromatic418967fa.accept_13_10_8_11_1_1985 10 216 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 216 271 (Polychromatic418967fa.accept_13_9_8_11_1_725 9 216 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 216 271 (accept_3_3 8 216 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 216 271 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 216 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 216 271
  (Polychromatic418967fa.accept_13_6_8_11_1_5398 6 216 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 216 271 (accept_3_3 5 216 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  216 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 216 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 216 271 (Polychromatic418967fa.accept_13_3_8_11_1_1906 3 216 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 216 271 (accept_3_3 2 216 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 216 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 216 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 216
  271)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 215 271 (Eq.refl Bool.true) (allA_of_3_1 57
  215 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 58 214 271 (Eq.refl Bool.true) (allA_succ_of_accept 57
  214 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 214 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 214 271 (accept_3_3 56 214 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 214 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 55 214 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 214 271 (Polychromatic418967fa.accept_21_12_4_19_1_4526 54 214
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 214 271 (accept_3_3 53 214
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 214 271
  (Polychromatic418967fa.accept_12_4_10_7_1_149 52 214 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 214 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 214 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 214 271 (accept_3_3 50 214 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 214 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 214 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 214 271 (Polychromatic418967fa.accept_7_6_4_5_1_314
  48 214 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 214 271 (accept_3_3 47
  214 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 214 271
  (Polychromatic418967fa.accept_18_10_16_1_1_1534 46 214 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 214 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 214 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 214 271 (accept_3_3 44 214 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 214 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 214 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 214 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 214 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 214 271 (accept_3_3 41 214 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 214 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 214 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 214 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 214 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 214 271 (accept_3_3 38 214 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 214 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 214 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 214 271
  (Polychromatic418967fa.accept_7_1_4_5_1_35 36 214 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 214 271 (accept_3_3 35 214 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 214 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 214 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 214 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 214 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 214 271 (accept_3_3 32 214 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 214 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 214 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 214 271
  (Polychromatic418967fa.accept_7_2_4_5_1_313 30 214 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 214 271 (accept_3_3 29 214 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 214 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 214 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 214 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 214 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 214 271 (accept_3_3 26 214 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 214 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 214 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 214 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 214 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 214 271 (accept_3_3 23 214 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 214 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 214 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 214 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 214 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 214 271 (accept_3_3 20 214 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 214 271 (Polychromatic418967fa.accept_24_19_22_7_1_8111 19 214 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 214 271
  (Polychromatic418967fa.accept_13_5_6_11_1_1933 18 214 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 214 271 (accept_3_3 17 214 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 214 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 214 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 214 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 214 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 214 271 (accept_3_3 14 214 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 214 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 214 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 214 271
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 214 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 214 271 (accept_3_3 11 214 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 214 271 (Polychromatic418967fa.accept_18_10_16_1_1_1534 10 214 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 214 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 214 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 214 271 (accept_3_3 8 214 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 214 271 (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 214 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 214 271
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 214 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 214 271 (accept_3_3 5 214 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  214 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 214 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 214 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 214 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 214 271 (accept_3_3 2 214 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 214 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 214 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 214
  271)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 213 271 (Eq.refl Bool.true)
  (allA_succ_of_accept 58 213 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 213 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 213 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 213 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 213 271 (accept_3_3 56 213 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 213 271 (Polychromatic418967fa.accept_13_3_5_11_1_716
  55 213 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 213 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 213 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 213 271 (accept_3_3 53 213 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 213 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 213 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 213 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 213 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 213 271 (accept_3_3 50 213 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 213 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 213 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 213 271
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 213 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 213 271 (accept_3_3 47 213 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 213 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 213 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 213 271 (Polychromatic418967fa.accept_13_6_5_11_1_1971 45 213 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 213 271 (accept_3_3 44 213 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 213 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 213 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 213 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 213 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 213 271 (accept_3_3 41 213 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 213 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 213 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 213 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 213 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 213 271 (accept_3_3 38 213 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 213 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 213 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 213 271
  (Polychromatic418967fa.accept_7_1_3_5_1_33 36 213 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 213 271 (accept_3_3 35 213 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 213 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 213 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 213 271 (Polychromatic418967fa.accept_13_7_5_11_1_1927 33 213 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 213 271 (accept_3_3 32 213 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 213 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 213 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 213 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 213 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 213 271 (accept_3_3 29 213 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 213 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 213 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 213 271 (Polychromatic418967fa.accept_12_3_9_7_1_472 27 213 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 213 271 (accept_3_3 26 213 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 213 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 213 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 213 271
  (Polychromatic418967fa.accept_20_4_13_11_1_12460 24 213 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 213 271 (accept_3_3 23 213 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 213 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 213 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 213 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 213 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 213 271 (accept_3_3 20 213 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 213 271 (Polychromatic418967fa.accept_11_8_4_7_1_1303
  19 213 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 213 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 213 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 213 271 (accept_3_3 17 213 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 213 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 213 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 213 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 213 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 213 271 (accept_3_3 14 213 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 213 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 213 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 213 271
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 213 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 213 271 (accept_3_3 11 213 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 213 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 213 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 213 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 213 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 213 271 (accept_3_3 8 213 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 213 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 213 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 213 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 213 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 213 271 (accept_3_3 5 213 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  213 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 213 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 213 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 213 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 213 271 (accept_3_3 2 213 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 213 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 213 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 213
  271))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 212 271 (Eq.refl Bool.true) (allA_of_3_1
  60 212 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 211 271 (Eq.refl Bool.true) (allA_succ_of_accept 60
  211 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 211 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 211 271 (accept_3_3 59 211 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 211 271 (Polychromatic418967fa.accept_21_16_1_19_1_10717 58 211 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 211 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 57
  211 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 211 271 (accept_3_3 56
  211 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 211 271
  (Polychromatic418967fa.accept_7_6_1_5_1_322 55 211 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 211 271 (Polychromatic418967fa.accept_13_2_3_11_1_1287 54 211 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 211 271 (accept_3_3 53 211 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 211 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 211 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 211 271 (Polychromatic418967fa.accept_9_6_4_1_1_390
  51 211 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 211 271 (accept_3_3 50
  211 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 211 271
  (Polychromatic418967fa.accept_13_10_3_11_1_1923 49 211 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 211 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 211 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 211 271 (accept_3_3 47 211 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 211 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 46 211 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 211 271
  (Polychromatic418967fa.accept_7_3_1_5_1_44 45 211 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 211 271 (accept_3_3 44 211 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 211 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 211 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 211 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 211 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 211 271 (accept_3_3 41 211 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 211 271 (Polychromatic418967fa.accept_13_1_3_11_1_1289 40 211 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 211 271
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 211 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 211 271 (accept_3_3 38 211 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 211 271 (Polychromatic418967fa.accept_17_3_7_16_1_3251 37 211 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 211 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 211 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 211 271 (accept_3_3 35 211 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 211 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 211 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 211 271
  (Polychromatic418967fa.accept_9_6_4_1_1_390 33 211 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 211 271 (accept_3_3 32 211 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 211 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 211 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 211 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 211 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 211 271 (accept_3_3 29 211 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 211 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 211 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 211 271
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 211 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 211 271 (accept_3_3 26 211 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 211 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 211 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 211 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 211 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 211 271 (accept_3_3 23 211 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 211 271 (Polychromatic418967fa.accept_19_3_2_5_1_5679 22 211 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 211 271
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 211 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 211 271 (accept_3_3 20 211 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 211 271 (Polychromatic418967fa.accept_22_19_13_7_1_5557 19 211 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 211 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 211 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 211 271 (accept_3_3 17 211 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 211 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 211 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 211 271
  (Polychromatic418967fa.accept_9_6_4_1_1_390 15 211 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 211 271 (accept_3_3 14 211 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 211 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 211 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 211 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 211 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 211 271 (accept_3_3 11 211 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 211 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 211 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 211 271
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 211 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 211 271 (accept_3_3 8 211 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  211 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 211 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 211 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 211 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 211 271 (accept_3_3 5 211 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 211 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 211 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 211 271
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 211 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 211 271 (accept_3_3 2 211 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  211 271 (Polychromatic418967fa.accept_13_1_3_11_1_1289 1 211 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 211 271))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 210 271
  (Eq.refl Bool.true) (allA_succ_of_accept 61 210 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 210 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 210 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 60 210 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 210 271 (accept_3_3 59 210 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 210 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 58 210 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 210 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 210 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 210 271 (accept_3_3 56 210 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 210 271 (Polychromatic418967fa.accept_13_3_2_11_1_1999 55 210 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 210 271
  (Polychromatic418967fa.accept_19_16_1_5_1_3084 54 210 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 210 271 (accept_3_3 53 210 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 210 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 210 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 210 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 210 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 210 271 (accept_3_3 50 210 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 210 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 210 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 210 271
  (Polychromatic418967fa.accept_13_9_2_11_1_1964 48 210 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 210 271 (accept_3_3 47 210 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 210 271 (Polychromatic418967fa.accept_29_17_7_10_1_16643 46 210 271 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 210 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 210 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 210 271 (accept_3_3 44 210 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 210 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 210 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 210 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 210 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 210 271 (accept_3_3 41 210 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 210 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 210 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 210 271 (Polychromatic418967fa.accept_11_6_1_7_1_1315 39 210 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 210 271 (accept_3_3 38 210 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 210 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 210 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 210 271
  (Polychromatic418967fa.accept_13_10_2_11_1_1920 36 210 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 210 271 (accept_3_3 35 210 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 210 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 210 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 210 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 210 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 210 271 (accept_3_3 32 210 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 210 271 (Polychromatic418967fa.accept_9_4_3_1_1_154
  31 210 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 210 271
  (Polychromatic418967fa.accept_13_4_2_11_1_733 30 210 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 210 271 (accept_3_3 29 210 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 210 271 (Polychromatic418967fa.accept_11_6_1_7_1_1315 28 210 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 210 271 (Polychromatic418967fa.accept_17_10_6_16_1_6862 27 210 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 210 271 (accept_3_3 26 210 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 210 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 210 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 210 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 210 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 210 271 (accept_3_3 23 210 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 210 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 210 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 210 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 210 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 210 271 (accept_3_3 20 210 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 210 271 (Polychromatic418967fa.accept_16_3_2_15_1_7367 19 210 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 210 271
  (Polychromatic418967fa.accept_19_18_1_5_1_5720 18 210 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 210 271 (accept_3_3 17 210 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 210 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 210 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 210 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 210 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 210 271 (accept_3_3 14 210 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 210 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 210 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 210 271
  (Polychromatic418967fa.accept_16_12_2_15_1_490 12 210 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 210 271 (accept_3_3 11 210 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 210 271 (Polychromatic418967fa.accept_13_10_2_11_1_1920 10 210 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 210 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 210 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 210 271 (accept_3_3 8 210 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 210 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 210 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 210 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 210 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 210 271 (accept_3_3 5 210 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  210 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 210 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 210 271 (Polychromatic418967fa.accept_13_3_2_11_1_1999 3 210 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 210 271 (accept_3_3 2 210 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 210 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 210 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 210
  271)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 209 271 (Eq.refl Bool.true)
  (allA_of_3_1 63 209 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 208 271 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 208 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 208 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 208 271 (accept_3_3 62 208 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 208 271 (Polychromatic418967fa.accept_19_4_18_5_1_929 61 208 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 208 271
  (Polychromatic418967fa.accept_22_16_10_7_1_5554 60 208 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 208 271 (accept_3_3 59 208 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 208 271 (Polychromatic418967fa.accept_11_3_10_7_1_129 58 208 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 208 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 208 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 208 271 (accept_3_3 56 208 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 208 271
  (Polychromatic418967fa.accept_15_10_13_1_1_3698 55 208 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 208 271 (Polychromatic418967fa.accept_17_3_4_16_1_3208 54 208 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 208 271 (accept_3_3 53 208 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 208 271 (Polychromatic418967fa.accept_14_10_12_5_1_3466 52 208
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 208 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 208 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 208 271 (accept_3_3 50 208 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 208 271 (Polychromatic418967fa.accept_10_9_8_1_1_1331 49 208 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 208 271 (Polychromatic418967fa.accept_15_3_13_1_1_479 48 208 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 208 271 (accept_3_3 47 208 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 208 271 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 208
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 208 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 208 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 208 271 (accept_3_3 44 208 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 208 271 (Polychromatic418967fa.accept_10_3_8_1_1_182 43 208 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 208 271 (Polychromatic418967fa.accept_15_12_13_1_1_3695 42 208 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 208 271 (accept_3_3 41 208 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 208 271 (Polychromatic418967fa.accept_15_10_13_1_1_3698 40 208
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 208 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 208 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 208 271 (accept_3_3 38 208 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 208 271 (Polychromatic418967fa.accept_17_3_4_16_1_3208 37 208 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 208 271 (Polychromatic418967fa.accept_11_3_10_7_1_129 36 208 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 208 271 (accept_3_3 35 208 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 208 271 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 208
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 208 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 208 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 208 271 (accept_3_3 32 208 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 208 271 (Polychromatic418967fa.accept_14_3_12_5_1_153 31 208 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 208 271 (Polychromatic418967fa.accept_22_8_10_7_1_16642 30 208 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 208 271 (accept_3_3 29 208 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 208 271 (Polychromatic418967fa.accept_19_9_18_5_1_7101 28 208
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 208 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 208 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 208 271 (accept_3_3 26 208 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 208 271 (Polychromatic418967fa.accept_11_3_10_7_1_129 25 208 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 208 271 (Polychromatic418967fa.accept_14_10_12_5_1_3466 24 208 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 208 271 (accept_3_3 23 208 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 208 271 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 208
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 208 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 208 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 208 271 (accept_3_3 20 208 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 208 271 (Polychromatic418967fa.accept_10_9_8_1_1_1331 19 208 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 208 271 (Polychromatic418967fa.accept_15_3_13_1_1_479 18 208 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 208 271 (accept_3_3 17 208 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 208 271 (Polychromatic418967fa.accept_18_16_10_1_1_3696 16 208
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 208 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 208 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 208 271 (accept_3_3 14 208 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 208 271 (Polychromatic418967fa.accept_10_3_8_1_1_182 13 208 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 208 271 (Polychromatic418967fa.accept_15_12_13_1_1_3695 12 208 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 208 271 (accept_3_3 11 208 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 208 271 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 208
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 208 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 208 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 208 271 (accept_3_3 8 208 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  208 271 (Polychromatic418967fa.accept_14_7_12_5_1_1861 7 208 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 208 271 (Polychromatic418967fa.accept_19_6_18_5_1_5630 6 208 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 208 271 (accept_3_3 5 208 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 208 271 (Polychromatic418967fa.accept_19_4_18_5_1_929 4 208 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 208 271
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 208 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 208 271 (accept_3_3 2 208 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  208 271 (Polychromatic418967fa.accept_19_1_18_5_1_5705 1 208 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 208 271)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 207 271
  (Eq.refl Bool.true) (allA_succ_of_accept 64 207 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 207 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 207 271
  (Polychromatic418967fa.accept_25_13_7_21_1_11411 63 207 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 207 271 (accept_3_3 62 207 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 207 271 (Polychromatic418967fa.accept_20_1_7_11_1_3673 61 207 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 207 271 (Polychromatic418967fa.accept_11_5_9_7_1_411 60 207
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 207 271 (accept_3_3 59 207
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 207 271
  (Polychromatic418967fa.accept_6_4_3_1_1_57 58 207 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 207 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 207 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 207 271 (accept_3_3 56 207 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 207 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 55 207 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 207 271 (Polychromatic418967fa.accept_10_4_7_1_1_471
  54 207 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 207 271 (accept_3_3 53
  207 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 207 271
  (Polychromatic418967fa.accept_6_4_3_1_1_57 52 207 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 207 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 207 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 207 271 (accept_3_3 50 207 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 207 271 (Polychromatic418967fa.accept_11_5_9_7_1_411 49 207 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 207 271
  (Polychromatic418967fa.accept_7_6_4_5_1_314 48 207 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 207 271 (accept_3_3 47 207 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 207 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 207 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 207 271 (Polychromatic418967fa.accept_12_9_3_7_1_924 45 207 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 207 271 (accept_3_3 44 207 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 207 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 207 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 207 271
  (Polychromatic418967fa.accept_18_6_9_1_1_3769 42 207 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 207 271 (accept_3_3 41 207 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 207 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 207 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 207 271 (Polychromatic418967fa.accept_18_3_9_1_1_3690 39 207 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 207 271 (accept_3_3 38 207 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 207 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 207 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 207 271
  (Polychromatic418967fa.accept_7_1_4_5_1_35 36 207 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 207 271 (accept_3_3 35 207 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 207 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 207 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 207 271 (Polychromatic418967fa.accept_12_9_3_7_1_924 33 207 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 207 271 (accept_3_3 32 207 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 207 271 (Polychromatic418967fa.accept_19_12_17_5_1_5702 31 207
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 207 271
  (Polychromatic418967fa.accept_7_2_4_5_1_313 30 207 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 207 271 (accept_3_3 29 207 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 207 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 207 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 207 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 207 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 207 271 (accept_3_3 26 207 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 207 271 (Polychromatic418967fa.accept_21_4_18_19_1_9189 25 207 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 207 271
  (Polychromatic418967fa.accept_10_4_7_1_1_471 24 207 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 207 271 (accept_3_3 23 207 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 207 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 207 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 207 271 (Polychromatic418967fa.accept_12_9_3_7_1_924 21 207 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 207 271 (accept_3_3 20 207 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 207 271 (Polychromatic418967fa.accept_15_4_12_1_1_1081 19 207
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 207 271
  (Polychromatic418967fa.accept_19_18_17_5_1_4343 18 207 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 207 271 (accept_3_3 17 207 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 207 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 207 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 207 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 207 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 207 271 (accept_3_3 14 207 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 207 271 (Polychromatic418967fa.accept_7_6_4_5_1_314
  13 207 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 207 271
  (Polychromatic418967fa.accept_19_12_17_5_1_5702 12 207 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 207 271 (accept_3_3 11 207 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 207 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 207 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 207 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 207 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 207 271 (accept_3_3 8 207 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 207 271
  (Polychromatic418967fa.accept_13_7_12_11_1_1911 7 207 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 207 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 207 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 207 271 (accept_3_3 5 207 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 207 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 207 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 207 271 (Polychromatic418967fa.accept_18_3_9_1_1_3690
  3 207 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 207 271 (accept_3_3 2
  207 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 207 271
  (Polychromatic418967fa.accept_7_1_4_5_1_35 1 207 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 207 271))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 206 271 (Eq.refl
  Bool.true) (allA_of_3_1 66 206 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 67 205 271 (Eq.refl Bool.true)
  (allA_succ_of_accept 66 205 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 205 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 205 271 (accept_3_3 65 205 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 205 271 (Polychromatic418967fa.accept_10_4_5_1_1_497 64 205 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 205 271
  (Polychromatic418967fa.accept_14_7_9_5_1_529 63 205 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 205 271 (accept_3_3 62 205 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 205 271 (Polychromatic418967fa.accept_19_4_15_5_1_3043 61 205 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 205 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 205 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 205 271 (accept_3_3 59 205 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 205 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 205 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 205 271
  (Polychromatic418967fa.accept_9_3_7_1_1_143 57 205 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 205 271 (accept_3_3 56 205 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 205 271 (Polychromatic418967fa.accept_13_3_10_11_1_1293 55 205 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 205 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 205 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 205 271 (accept_3_3 53 205 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 205 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 52 205 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 205 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 51 205 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 205 271 (accept_3_3 50 205 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 205 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 205 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 205 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 48 205 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 205 271 (accept_3_3 47 205 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 205 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 205 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 205 271
  (Polychromatic418967fa.accept_7_3_2_5_1_147 45 205 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 205 271 (accept_3_3 44 205 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 205 271 (Polychromatic418967fa.accept_13_4_10_11_1_1908 43 205 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 205 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 205 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 205 271 (accept_3_3 41 205 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 205 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 205 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 205 271
  (Polychromatic418967fa.accept_7_4_2_5_1_527 39 205 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 205 271 (accept_3_3 38 205 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 205 271 (Polychromatic418967fa.accept_15_7_10_1_1_1836 37 205 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 205 271 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 205 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 205 271 (accept_3_3 35 205 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 205 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 205 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 205 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 33 205 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 205 271 (accept_3_3 32 205 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 205 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 205 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 205 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 205 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 205 271 (accept_3_3 29 205 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 205 271 (Polychromatic418967fa.accept_13_2_10_11_1_1276 28 205 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 205 271
  (Polychromatic418967fa.accept_13_1_10_11_1_1280 27 205 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 205 271 (accept_3_3 26 205 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 205 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 205 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 205 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 205 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 205 271 (accept_3_3 23 205 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 205 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 22
  205 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 205 271
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 205 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 205 271 (accept_3_3 20 205 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 205 271 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 205 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 205 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 205 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 205 271 (accept_3_3 17 205 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 205 271 (Polychromatic418967fa.accept_10_6_5_1_1_482 16 205 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 205 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 15 205 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 205 271 (accept_3_3 14 205 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 205 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 205 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 205 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 205 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 205 271 (accept_3_3 11 205 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 205 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 205 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 205 271
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 205 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 205 271 (accept_3_3 8 205 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  205 271 (Polychromatic418967fa.accept_14_7_9_5_1_529 7 205 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 205 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 205 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 205 271 (accept_3_3 5 205 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 205 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 205 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 205 271
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 205 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 205 271 (accept_3_3 2 205 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  205 271 (Polychromatic418967fa.accept_13_1_10_11_1_1280 1 205 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 205 271))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 204
  271 (Eq.refl Bool.true) (allA_succ_of_accept 67 204 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 67 204 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 204 271
  (Polychromatic418967fa.accept_7_3_1_5_1_44 66 204 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 204 271 (accept_3_3 65 204 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 204 271 (Polychromatic418967fa.accept_21_1_15_19_1_4491 64 204 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 204 271 (Polychromatic418967fa.accept_18_9_6_1_1_3687 63 204 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 204 271 (accept_3_3 62 204 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 204 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 61 204 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 204 271
  (Polychromatic418967fa.accept_7_4_1_5_1_540 60 204 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 204 271 (accept_3_3 59 204 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 204 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 204 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 204 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 204 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 204 271 (accept_3_3 56 204 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 204 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 55 204 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 204 271
  (Polychromatic418967fa.accept_13_2_9_11_1_258 54 204 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 204 271 (accept_3_3 53 204 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 204 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 204 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 204 271 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 204 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 204 271 (accept_3_3 50 204 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 204 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 204 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 204 271
  (Polychromatic418967fa.accept_7_6_1_5_1_322 48 204 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 204 271 (accept_3_3 47 204 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 204 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 46 204 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 204 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 204 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 204 271 (accept_3_3 44 204 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 204 271 (Polychromatic418967fa.accept_8_3_4_7_1_475 43 204 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 204 271
  (Polychromatic418967fa.accept_24_18_12_7_1_14861 42 204 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 204 271 (accept_3_3 41 204 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 204 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 204 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 204 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 204 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 204 271 (accept_3_3 38 204 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 204 271 (Polychromatic418967fa.accept_10_7_4_1_1_1319
  37 204 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 204 271
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 36 204 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 204 271 (accept_3_3 35 204 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 204 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 204 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 204 271 (Polychromatic418967fa.accept_13_7_9_11_1_705 33 204 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 204 271 (accept_3_3 32 204 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 204 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 204 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 204 271
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 204 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 204 271 (accept_3_3 29 204 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 204 271 (Polychromatic418967fa.accept_13_2_9_11_1_258 28 204 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 204 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 204 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 204 271 (accept_3_3 26 204 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 204 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 204 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 204 271
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 204 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 204 271 (accept_3_3 23 204 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 204 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 204 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 204 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 204 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 204 271 (accept_3_3 20 204 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 204 271 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 204 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 204 271
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 204 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 204 271 (accept_3_3 17 204 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 204 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 204 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 204 271 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 204 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 204 271 (accept_3_3 14 204 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 204 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 204 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 204 271
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 204 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 204 271 (accept_3_3 11 204 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 204 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 204 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 204 271 (Polychromatic418967fa.accept_18_9_6_1_1_3687 9 204 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 204 271 (accept_3_3 8 204 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 204 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 204 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 204 271
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 204 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 204 271 (accept_3_3 5 204 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  204 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 204 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 204 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 204 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 204 271 (accept_3_3 2 204 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 204 271 (Polychromatic418967fa.accept_11_1_6_7_1_116 1 204 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 204
  271)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 203 271 (Eq.refl Bool.true)
  (allA_of_3_1 69 203 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 70 202 271 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 202 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 202 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 202 271 (accept_3_3 68 202 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 202 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 67 202 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 202 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 66
  202 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 202 271 (accept_3_3 65
  202 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 202 271
  (Polychromatic418967fa.accept_7_1_6_5_1_39 64 202 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 202 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 202 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 202 271 (accept_3_3 62 202 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 202 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 202 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 202 271 (Polychromatic418967fa.accept_7_4_6_5_1_141
  60 202 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 202 271 (accept_3_3 59
  202 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 202 271
  (Polychromatic418967fa.accept_11_3_4_7_1_114 58 202 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 202 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 202 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 202 271 (accept_3_3 56 202 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 202 271 (Polychromatic418967fa.accept_13_3_7_11_1_1904 55 202 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 202 271
  (Polychromatic418967fa.accept_15_9_7_1_1_1075 54 202 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 202 271 (accept_3_3 53 202 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 202 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 202 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 202 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 202 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 202 271 (accept_3_3 50 202 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 202 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 202 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 202 271
  (Polychromatic418967fa.accept_9_3_4_1_1_22 48 202 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 202 271 (accept_3_3 47 202 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 202 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 202 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 202 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 202 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 202 271 (accept_3_3 44 202 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 202 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 202 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 202 271
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 202 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 202 271 (accept_3_3 41 202 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 202 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 202 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 202 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 202 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 202 271 (accept_3_3 38 202 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 202 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 202 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 202 271
  (Polychromatic418967fa.accept_7_1_6_5_1_39 36 202 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 202 271 (accept_3_3 35 202 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 202 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 202 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 202 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 202 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 202 271 (accept_3_3 32 202 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 202 271 (Polychromatic418967fa.accept_13_5_7_11_1_3470 31 202 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 202 271
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 202 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 202 271 (accept_3_3 29 202 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 202 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 202 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 202 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 202 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 202 271 (accept_3_3 26 202 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 202 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 202 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 202 271
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 202 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 202 271 (accept_3_3 23 202 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 202 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 202 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 202 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 202 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 202 271 (accept_3_3 20 202 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 202 271 (Polychromatic418967fa.accept_10_9_2_1_1_840 19 202 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 202 271
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 202 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 202 271 (accept_3_3 17 202 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 202 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 202 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 202 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 202 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 202 271 (accept_3_3 14 202 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 202 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 202 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 202 271
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 202 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 202 271 (accept_3_3 11 202 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 202 271 (Polychromatic418967fa.accept_15_10_7_1_1_3686 10 202 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 202 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 202 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 202 271 (accept_3_3 8 202 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 202 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 202 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 202 271
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 202 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 202 271 (accept_3_3 5 202 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  202 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 202 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 202 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 202 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 202 271 (accept_3_3 2 202 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 202 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 202 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 202
  271)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 201 271 (Eq.refl Bool.true)
  (allA_succ_of_accept 70 201 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 201 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 201 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 201 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 201 271 (accept_3_3 68 201 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 201 271 (Polychromatic418967fa.accept_9_4_3_1_1_154
  67 201 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 201 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 201 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 201 271 (accept_3_3 65 201 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 201 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 201 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 201 271 (Polychromatic418967fa.accept_12_3_9_7_1_472 63 201 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 201 271 (accept_3_3 62 201 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 201 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 61 201 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 201 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 60 201 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 201 271 (accept_3_3 59 201 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 201 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 201 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 201 271 (Polychromatic418967fa.accept_13_5_6_11_1_1933 57 201 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 201 271 (accept_3_3 56 201 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 201 271 (Polychromatic418967fa.accept_15_10_6_1_1_3707 55 201
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 201 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 201 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 201 271 (accept_3_3 53 201 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 201 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 201 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 201 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 201 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 201 271 (accept_3_3 50 201 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 201 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 201 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 201 271
  (Polychromatic418967fa.accept_11_4_3_7_1_828 48 201 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 201 271 (accept_3_3 47 201 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 201 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 201 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 201 271 (Polychromatic418967fa.accept_17_11_14_16_1_1270 45 201 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 201 271 (accept_3_3 44 201 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 201 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 201 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 201 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 201 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 201 271 (accept_3_3 41 201 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 201 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 201 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 201 271 (Polychromatic418967fa.accept_12_3_9_7_1_472 39 201 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 201 271 (accept_3_3 38 201 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 201 271 (Polychromatic418967fa.accept_11_4_3_7_1_828 37 201
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 201 271
  (Polychromatic418967fa.accept_17_2_14_16_1_2187 36 201 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 201 271 (accept_3_3 35 201 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 201 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 201 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 201 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 201 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 201 271 (accept_3_3 32 201 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 201 271 (Polychromatic418967fa.accept_9_4_3_1_1_154
  31 201 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 201 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 201 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 201 271 (accept_3_3 29 201 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 201 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 201 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 201 271 (Polychromatic418967fa.accept_12_3_9_7_1_472 27 201 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 201 271 (accept_3_3 26 201 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 201 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 201 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 201 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 201 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 201 271 (accept_3_3 23 201 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 201 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 201 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 201 271 (Polychromatic418967fa.accept_11_10_3_7_1_2564 21 201 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 201 271 (accept_3_3 20 201 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 201 271 (Polychromatic418967fa.accept_17_2_14_16_1_2187 19 201
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 201 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 201 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 201 271 (accept_3_3 17 201 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 201 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 201 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 201 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 201 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 201 271 (accept_3_3 14 201 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 201 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 201 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 201 271
  (Polychromatic418967fa.accept_18_12_3_1_1_3685 12 201 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 201 271 (accept_3_3 11 201 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 201 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 201 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 201 271 (Polychromatic418967fa.accept_15_9_6_1_1_493 9 201 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 201 271 (accept_3_3 8 201 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 201 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 201 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 201 271
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 201 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 201 271 (accept_3_3 5 201 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  201 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 201 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 201 271 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 201 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 201 271 (accept_3_3 2 201 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 201 271 (Polychromatic418967fa.accept_21_1_12_19_1_7721 1 201 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 201
  271))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 200 271 (Eq.refl Bool.true)
  (allA_of_3_1 72 200 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 73 199 271 (Eq.refl Bool.true)
  (allA_succ_of_accept 72 199 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 199 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 199 271 (accept_3_3 71 199 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 199 271 (Polychromatic418967fa.accept_16_6_7_15_1_1942 70 199 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 199 271
  (Polychromatic418967fa.accept_17_1_12_16_1_2211 69 199 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 199 271 (accept_3_3 68 199 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 199 271 (Polychromatic418967fa.accept_13_2_4_11_1_2003 67 199 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 199 271 (Polychromatic418967fa.accept_23_20_15_18_1_16641 66
  199 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 199 271 (accept_3_3 65
  199 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 199 271
  (Polychromatic418967fa.accept_7_1_3_5_1_33 64 199 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 199 271 (Polychromatic418967fa.accept_15_3_4_1_1_1072 63 199 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 199 271 (accept_3_3 62 199 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 199 271 (Polychromatic418967fa.accept_11_6_1_7_1_1315 61 199 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 199 271
  (Polychromatic418967fa.accept_13_8_4_11_1_3469 60 199 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 199 271 (accept_3_3 59 199 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 199 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 58 199 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 199 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 199 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 199 271 (accept_3_3 56 199 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 199 271 (Polychromatic418967fa.accept_10_5_9_1_1_187 55 199 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 199 271
  (Polychromatic418967fa.accept_13_2_4_11_1_2003 54 199 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 199 271 (accept_3_3 53 199 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 199 271 (Polychromatic418967fa.accept_10_2_9_1_1_185 52 199 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 199 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 199 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 199 271 (accept_3_3 50 199 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 199 271 (Polychromatic418967fa.accept_13_10_4_11_1_1969 49 199 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 199 271
  (Polychromatic418967fa.accept_10_8_9_1_1_189 48 199 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 199 271 (accept_3_3 47 199 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 199 271 (Polychromatic418967fa.accept_13_7_4_11_1_1967 46 199 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 199 271 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 199 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 199 271 (accept_3_3 44 199 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 199 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 199 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 199 271
  (Polychromatic418967fa.accept_10_2_9_1_1_185 42 199 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 199 271 (accept_3_3 41 199 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 199 271 (Polychromatic418967fa.accept_14_12_3_5_1_1868 40 199 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 199 271 (Polychromatic418967fa.accept_11_6_1_7_1_1315 39 199 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 199 271 (accept_3_3 38 199 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 199 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 199 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 199 271
  (Polychromatic418967fa.accept_7_1_3_5_1_33 36 199 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 199 271 (accept_3_3 35 199 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 199 271 (Polychromatic418967fa.accept_13_8_4_11_1_3469 34 199 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 199 271 (Polychromatic418967fa.accept_13_7_4_11_1_1967 33 199 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 199 271 (accept_3_3 32 199 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 199 271 (Polychromatic418967fa.accept_19_12_9_5_1_8593 31 199
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 199 271
  (Polychromatic418967fa.accept_7_2_3_5_1_34 30 199 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 199 271 (accept_3_3 29 199 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 199 271 (Polychromatic418967fa.accept_10_8_9_1_1_189 28 199 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 199 271 (Polychromatic418967fa.accept_15_12_4_1_1_3746 27 199 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 199 271 (accept_3_3 26 199 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 199 271 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 199
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 199 271
  (Polychromatic418967fa.accept_16_8_7_15_1_6339 24 199 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 199 271 (accept_3_3 23 199 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 199 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 199 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 199 271 (Polychromatic418967fa.accept_13_8_4_11_1_3469 21 199 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 199 271 (accept_3_3 20 199 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 199 271 (Polychromatic418967fa.accept_13_6_4_11_1_282 19 199
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 199 271
  (Polychromatic418967fa.accept_10_8_9_1_1_189 18 199 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 199 271 (accept_3_3 17 199 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 199 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 199 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 199 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 199 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 199 271 (accept_3_3 14 199 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 199 271 (Polychromatic418967fa.accept_17_13_12_16_1_6908 13 199 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 199 271
  (Polychromatic418967fa.accept_10_2_9_1_1_185 12 199 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 199 271 (accept_3_3 11 199 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 199 271 (Polychromatic418967fa.accept_13_10_4_11_1_1969 10 199 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 199 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 199 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 199 271 (accept_3_3 8 199 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 199 271 (Polychromatic418967fa.accept_13_7_4_11_1_1967 7 199 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 199 271
  (Polychromatic418967fa.accept_11_6_1_7_1_1315 6 199 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 199 271 (accept_3_3 5 199 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  199 271 (Polychromatic418967fa.accept_19_4_9_5_1_8572 4 199 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 199 271 (Polychromatic418967fa.accept_15_3_4_1_1_1072 3 199 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 199 271 (accept_3_3 2 199 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 199 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 199 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 199
  271))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 198 271 (Eq.refl
  Bool.true) (allA_succ_of_accept 73 198 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 198 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 198 271 (Polychromatic418967fa.accept_13_7_3_11_1_280
  72 198 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 198 271 (accept_3_3 71
  198 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 198 271
  (Polychromatic418967fa.accept_13_5_3_11_1_1288 70 198 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 198 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 198 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 198 271 (accept_3_3 68 198 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 198 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 67 198 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 198 271 (Polychromatic418967fa.accept_7_3_2_5_1_147
  66 198 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 198 271 (accept_3_3 65
  198 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 198 271
  (Polychromatic418967fa.accept_15_4_3_1_1_487 64 198 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 198 271 (Polychromatic418967fa.accept_10_3_8_1_1_182 63 198 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 198 271 (accept_3_3 62 198 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 198 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 198 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 198 271 (Polychromatic418967fa.accept_7_4_2_5_1_527
  60 198 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 198 271 (accept_3_3 59
  198 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 198 271
  (Polychromatic418967fa.accept_15_13_3_1_1_3740 58 198 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 198 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 198 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 198 271 (accept_3_3 56 198 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 198 271 (Polychromatic418967fa.accept_16_7_6_15_1_495 55 198 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 198 271
  (Polychromatic418967fa.accept_13_2_3_11_1_1287 54 198 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 198 271 (accept_3_3 53 198 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 198 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 52 198 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 198 271 (Polychromatic418967fa.accept_15_6_3_1_1_3678 51 198 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 198 271 (accept_3_3 50 198 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 198 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 198 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 198 271
  (Polychromatic418967fa.accept_17_14_11_16_1_3261 48 198 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 198 271 (accept_3_3 47 198 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 198 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 46 198 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 198 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 198 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 198 271 (accept_3_3 44 198 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 198 271 (Polychromatic418967fa.accept_10_3_8_1_1_182
  43 198 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 198 271
  (Polychromatic418967fa.accept_19_4_8_5_1_5636 42 198 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 198 271 (accept_3_3 41 198 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 198 271 (Polychromatic418967fa.accept_13_1_3_11_1_1289 40 198 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 198 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 198 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 198 271 (accept_3_3 38 198 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 198 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 198 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 198 271
  (Polychromatic418967fa.accept_13_10_3_11_1_1923 36 198 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 198 271 (accept_3_3 35 198 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 198 271 (Polychromatic418967fa.accept_13_8_3_11_1_3467 34 198 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 198 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 198 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 198 271 (accept_3_3 32 198 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 198 271 (Polychromatic418967fa.accept_7_3_2_5_1_147
  31 198 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 198 271
  (Polychromatic418967fa.accept_23_7_14_18_1_16640 30 198 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 198 271 (accept_3_3 29 198 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 198 271 (Polychromatic418967fa.accept_13_2_3_11_1_1287 28 198 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 198 271 (Polychromatic418967fa.accept_13_1_3_11_1_1289 27 198
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 198 271 (accept_3_3 26 198
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 198 271 (Polychromatic418967fa.accept_4_1_2_3_1_9
  25 198 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 198 271
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 198 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 198 271 (accept_3_3 23 198 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 198 271 (Polychromatic418967fa.accept_17_5_11_16_1_3257 22 198 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 198 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 198 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 198 271 (accept_3_3 20 198 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 198 271 (Polychromatic418967fa.accept_10_9_8_1_1_1331 19 198 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 198 271
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 198 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 198 271 (accept_3_3 17 198 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 198 271 (Polychromatic418967fa.accept_19_16_8_5_1_4322 16 198 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 198 271 (Polychromatic418967fa.accept_13_2_3_11_1_1287 15 198 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 198 271 (accept_3_3 14 198 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 198 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 198 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 198 271
  (Polychromatic418967fa.accept_17_12_11_16_1_6903 12 198 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 198 271 (accept_3_3 11 198 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 198 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 198 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 198 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 198 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 198 271 (accept_3_3 8 198 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 198 271 (Polychromatic418967fa.accept_13_7_3_11_1_280
  7 198 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 198 271
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 6 198 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 198 271 (accept_3_3 5 198 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  198 271 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 198 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 198 271 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 198 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 198 271 (accept_3_3 2 198 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 198 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 198 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 198
  271)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 197 271 (Eq.refl
  Bool.true) (allA_of_3_1 75 197 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 76 196 271 (Eq.refl Bool.true)
  (allA_succ_of_accept 75 196 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 196 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 196 271 (accept_3_3 74 196 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 196 271 (Polychromatic418967fa.accept_13_8_1_11_1_1284 73 196 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 196 271
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 72 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 196 271 (accept_3_3 71 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 196 271 (Polychromatic418967fa.accept_12_10_4_7_1_948 70 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 196 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 196 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 196 271 (accept_3_3 68 196 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 196 271 (Polychromatic418967fa.accept_8_3_4_7_1_475 67 196 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 196 271
  (Polychromatic418967fa.accept_9_3_7_1_1_143 66 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 196 271 (accept_3_3 65 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 196 271 (Polychromatic418967fa.accept_13_12_1_11_1_1917 64 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 196 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 196 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 196 271 (accept_3_3 62 196 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 196 271 (Polychromatic418967fa.accept_13_9_1_11_1_275 61 196 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 196 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 60 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 196 271 (accept_3_3 59 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 196 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 196 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 196 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 196 271 (accept_3_3 56 196 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 196 271 (Polychromatic418967fa.accept_10_5_6_1_1_836 55 196 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 196 271
  (Polychromatic418967fa.accept_21_12_7_19_1_10736 54 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 196 271 (accept_3_3 53 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 196 271 (Polychromatic418967fa.accept_10_2_6_1_1_1296 52 196 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 196 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 196 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 196 271 (accept_3_3 50 196 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 196 271 (Polychromatic418967fa.accept_9_4_7_1_1_379
  49 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 196 271
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 196 271 (accept_3_3 47 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 196 271 (Polychromatic418967fa.accept_11_2_9_7_1_124 46 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 196 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 196 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 196 271 (accept_3_3 44 196 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 196 271 (Polychromatic418967fa.accept_8_3_4_7_1_475 43 196 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 196 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 196 271 (accept_3_3 41 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 196 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 196 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 196 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 196 271 (accept_3_3 38 196 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 196 271 (Polychromatic418967fa.accept_10_7_6_1_1_486 37 196 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 196 271
  (Polychromatic418967fa.accept_13_10_1_11_1_1961 36 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 196 271 (accept_3_3 35 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 196 271 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 196 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 196 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 196 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 196 271 (accept_3_3 32 196 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 196 271 (Polychromatic418967fa.accept_9_4_7_1_1_379
  31 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 196 271
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 196 271 (accept_3_3 29 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 196 271 (Polychromatic418967fa.accept_16_12_4_15_1_5091 28 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 196 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 196 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 196 271 (accept_3_3 26 196 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 196 271 (Polychromatic418967fa.accept_10_5_6_1_1_836 25 196 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 196 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 196 271 (accept_3_3 23 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 196 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 196 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 196 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 196 271 (accept_3_3 20 196 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 196 271 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 196 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 196 271
  (Polychromatic418967fa.accept_19_18_6_5_1_4321 18 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 196 271 (accept_3_3 17 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 196 271 (Polychromatic418967fa.accept_11_5_9_7_1_411 16 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 196 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 196 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 196 271 (accept_3_3 14 196 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 196 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 196 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 196 271
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 196 271 (accept_3_3 11 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 196 271 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 196 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 196 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 196 271 (accept_3_3 8 196 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 196 271 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 196 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 196 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 196 271 (accept_3_3 5 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  196 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 196 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 196 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 196 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 196 271 (accept_3_3 2 196 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 196 271 (Polychromatic418967fa.accept_19_1_6_5_1_4319 1 196 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 196
  271)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 195 271 (Eq.refl
  Bool.true) (allA_succ_of_accept 76 195 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 195 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 195 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 75
  195 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 195 271 (accept_3_3 74
  195 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 195 271
  (Polychromatic418967fa.accept_20_13_15_11_1_6610 73 195 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 195 271 (Polychromatic418967fa.accept_26_20_13_11_1_13010 72 195 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 195 271 (accept_3_3 71 195 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 195 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 195 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 195 271
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 69 195 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 195 271 (accept_3_3 68 195 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 195 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 67 195 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 195 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 66 195 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 195 271 (accept_3_3 65 195 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 195 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 195 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 195 271
  (Polychromatic418967fa.accept_25_13_20_21_1_9709 63 195 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 195 271 (accept_3_3 62 195 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 195 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 61 195 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 195 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 195 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 195 271 (accept_3_3 59 195 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 195 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 58
  195 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 195 271
  (Polychromatic418967fa.accept_7_1_6_5_1_39 57 195 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 195 271 (accept_3_3 56 195 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 195 271 (Polychromatic418967fa.accept_16_7_3_15_1_2940 55 195 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 195 271 (Polychromatic418967fa.accept_10_4_5_1_1_497 54 195 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 195 271 (accept_3_3 53 195 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 195 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 195 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 195 271
  (Polychromatic418967fa.accept_23_5_11_18_1_16639 51 195 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 195 271 (accept_3_3 50 195 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 195 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 195 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 195 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 195 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 195 271 (accept_3_3 47 195 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 195 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 46
  195 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 195 271
  (Polychromatic418967fa.accept_12_9_3_7_1_924 45 195 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 195 271 (accept_3_3 44 195 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 195 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 195 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 195 271 (Polychromatic418967fa.accept_25_17_20_21_1_16638 42 195 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 195 271 (accept_3_3 41 195 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 195 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 195 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 195 271
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 195 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 195 271 (accept_3_3 38 195 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 195 271 (Polychromatic418967fa.accept_11_4_8_7_1_819 37 195 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 195 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 195 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 195 271 (accept_3_3 35 195 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 195 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 195 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 195 271
  (Polychromatic418967fa.accept_12_9_3_7_1_924 33 195 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 195 271 (accept_3_3 32 195 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 195 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 195 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 195 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 195 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 195 271 (accept_3_3 29 195 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 195 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 195 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 195 271
  (Polychromatic418967fa.accept_16_11_3_15_1_1989 27 195 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 195 271 (accept_3_3 26 195 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 195 271 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 195 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 195 271 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 195
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 195 271 (accept_3_3 23 195
  271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 195 271
  (Polychromatic418967fa.accept_6_4_3_1_1_57 22 195 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 195 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 195 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 195 271 (accept_3_3 20 195 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 195 271 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 195 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 195 271
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 195 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 195 271 (accept_3_3 17 195 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 195 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 195 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 195 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 195 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 195 271 (accept_3_3 14 195 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 195 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 195 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 195 271
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 195 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 195 271 (accept_3_3 11 195 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 195 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 195 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 195 271 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 195 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 195 271 (accept_3_3 8 195 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 195 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 195 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 195 271
  (Polychromatic418967fa.accept_10_6_5_1_1_482 6 195 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 195 271 (accept_3_3 5 195 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  195 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 195 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 195 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 195 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 195 271 (accept_3_3 2 195 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 195 271 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 195 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 195
  271))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 78 194 271 (Eq.refl
  Bool.true) (allA_of_3_1 78 194 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 79 193 271 (Eq.refl Bool.true)
  (allA_succ_of_accept 78 193 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 193 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 193 271 (accept_3_3 77 193 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 193 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 76 193 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 193 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 75
  193 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 193 271 (accept_3_3 74
  193 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 193 271
  (Polychromatic418967fa.accept_19_16_3_5_1_5684 73 193 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 193 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 72 193 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 193 271 (accept_3_3 71 193 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 193 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 193 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 193 271 (Polychromatic418967fa.accept_7_6_4_5_1_314
  69 193 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 193 271 (accept_3_3 68
  193 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 193 271
  (Polychromatic418967fa.accept_11_1_6_7_1_116 67 193 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 193 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 193 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 193 271 (accept_3_3 65 193 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 193 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 64 193 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 193 271 (Polychromatic418967fa.accept_15_3_13_1_1_479
  63 193 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 193 271 (accept_3_3 62
  193 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 193 271
  (Polychromatic418967fa.accept_9_7_4_1_1_391 61 193 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 193 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 60 193 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 193 271 (accept_3_3 59 193 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 193 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 193 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 193 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 57
  193 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 193 271 (accept_3_3 56
  193 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 193 271
  (Polychromatic418967fa.accept_7_6_4_5_1_314 55 193 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 193 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 193 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 193 271 (accept_3_3 53 193 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 193 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 193 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 193 271 (Polychromatic418967fa.accept_7_2_4_5_1_313
  51 193 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 193 271 (accept_3_3 50
  193 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 193 271
  (Polychromatic418967fa.accept_21_7_4_19_1_4525 49 193 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 193 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 193 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 193 271 (accept_3_3 47 193 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 193 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 193 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 193 271 (Polychromatic418967fa.accept_11_1_6_7_1_116
  45 193 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 193 271 (accept_3_3 44
  193 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 193 271
  (Polychromatic418967fa.accept_7_1_4_5_1_35 43 193 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 193 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 193 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 193 271 (accept_3_3 41 193 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 193 271 (Polychromatic418967fa.accept_15_10_13_1_1_3698 40 193 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 193 271
  (Polychromatic418967fa.accept_9_3_4_1_1_22 39 193 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 193 271 (accept_3_3 38 193 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 193 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 193 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 193 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 193 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 193 271 (accept_3_3 35 193 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 193 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 193 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 193 271
  (Polychromatic418967fa.accept_9_6_4_1_1_390 33 193 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 193 271 (accept_3_3 32 193 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 193 271 (Polychromatic418967fa.accept_21_10_4_19_1_3136 31 193 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 193 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 193 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 193 271 (accept_3_3 29 193 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 193 271 (Polychromatic418967fa.accept_10_8_3_1_1_1316 28 193 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 193 271
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 193 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 193 271 (accept_3_3 26 193 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 193 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 193 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 193 271 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 193 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 193 271 (accept_3_3 23 193 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 193 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 193 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 193 271
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 193 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 193 271 (accept_3_3 20 193 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 193 271 (Polychromatic418967fa.accept_22_19_17_7_1_13549 19 193 271 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 193 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 193 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 193 271 (accept_3_3 17 193 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 193 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 193 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 193 271
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 193 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 193 271 (accept_3_3 14 193 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 193 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 193 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 193 271 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 193 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 193 271 (accept_3_3 11 193 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 193 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 193 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 193 271
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 193 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 193 271 (accept_3_3 8 193 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  193 271 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 193 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 193 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 193 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 193 271 (accept_3_3 5 193 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 193 271 (Polychromatic418967fa.accept_20_4_13_11_1_12460 4 193 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 193 271
  (Polychromatic418967fa.accept_9_3_4_1_1_22 3 193 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 193 271 (accept_3_3 2 193 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  193 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 193 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 193 271)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 80 192 271 (Eq.refl Bool.true) (allA_succ_of_accept 79 192 271 (Polychromatic418967fa.accept_7_2_3_5_1_34
  79 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 192 271
  (Polychromatic418967fa.accept_7_1_3_5_1_33 78 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 192 271 (accept_3_3 77 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 192 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 76 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 192 271 (Polychromatic418967fa.accept_11_9_5_7_1_815 75 192 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 192 271 (accept_3_3 74 192 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 192 271 (Polychromatic418967fa.accept_10_3_2_1_1_839 73 192
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 192 271
  (Polychromatic418967fa.accept_7_2_3_5_1_34 72 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 192 271 (accept_3_3 71 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 192 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 70 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 192 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 192 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 192 271 (accept_3_3 68 192 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 192 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 67 192 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 192 271
  (Polychromatic418967fa.accept_10_6_2_1_1_494 66 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 192 271 (accept_3_3 65 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 192 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 64 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 192 271 (Polychromatic418967fa.accept_10_3_2_1_1_839 63 192 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 192 271 (accept_3_3 62 192 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 192 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 61 192 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 192 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 60 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 192 271 (accept_3_3 59 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 192 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 58 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 192 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 192 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 192 271 (accept_3_3 56 192 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 192 271 (Polychromatic418967fa.accept_13_3_10_11_1_1293 55 192 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 192 271
  (Polychromatic418967fa.accept_13_2_10_11_1_1276 54 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 192 271 (accept_3_3 53 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 192 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 192 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 192 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 192 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 192 271 (accept_3_3 50 192 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 192 271 (Polychromatic418967fa.accept_9_4_3_1_1_154
  49 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 192 271
  (Polychromatic418967fa.accept_19_10_2_5_1_3059 48 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 192 271 (accept_3_3 47 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 192 271 (Polychromatic418967fa.accept_10_6_2_1_1_494 46 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 192 271 (Polychromatic418967fa.accept_17_11_5_16_1_5600 45 192 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 192 271 (accept_3_3 44 192 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 192 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 192 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 192 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 192 271 (accept_3_3 41 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 192 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 192 271 (Polychromatic418967fa.accept_10_9_2_1_1_840 39 192 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 192 271 (accept_3_3 38 192 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 192 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 192 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 192 271
  (Polychromatic418967fa.accept_7_1_3_5_1_33 36 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 192 271 (accept_3_3 35 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 192 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 192 271 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 192 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 192 271 (accept_3_3 32 192 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 192 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 192 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 192 271
  (Polychromatic418967fa.accept_7_2_3_5_1_34 30 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 192 271 (accept_3_3 29 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 192 271 (Polychromatic418967fa.accept_13_2_10_11_1_1276 28 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 192 271 (Polychromatic418967fa.accept_13_1_10_11_1_1280 27 192 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 192 271 (accept_3_3 26 192 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 192 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 192 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 192 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 192 271 (accept_3_3 23 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 192 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 192 271 (Polychromatic418967fa.accept_13_8_10_11_1_2730 21 192 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 192 271 (accept_3_3 20 192 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 192 271 (Polychromatic418967fa.accept_10_9_2_1_1_840 19 192
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 192 271
  (Polychromatic418967fa.accept_17_1_5_16_1_5589 18 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 192 271 (accept_3_3 17 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 192 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 192 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 192 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 192 271 (accept_3_3 14 192 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 192 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 192 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 192 271
  (Polychromatic418967fa.accept_13_12_10_11_1_1279 12 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 192 271 (accept_3_3 11 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 192 271 (Polychromatic418967fa.accept_19_10_2_5_1_3059 10 192 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 192 271 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 192 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 192 271 (accept_3_3 8 192 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 192 271 (Polychromatic418967fa.accept_9_7_3_1_1_386 7
  192 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 192 271
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 192 271 (accept_3_3 5 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  192 271 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 192 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 192 271 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 192 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 192 271 (accept_3_3 2 192 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 192 271 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 192 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 192
  271)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 81 191 271 (Eq.refl
  Bool.true) (allA_of_3_1 81 191 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 82 190 271 (Eq.refl Bool.true)
  (allA_succ_of_accept 81 190 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 190 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 190 271 (accept_3_3 80 190 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 190 271 (Polychromatic418967fa.accept_13_1_8_11_1_724 79 190 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 190 271
  (Polychromatic418967fa.accept_21_15_1_19_1_9205 78 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 190 271 (accept_3_3 77 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 190 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 76 190 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 190 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 190 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 190 271 (accept_3_3 74 190 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 190 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 73
  190 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 190 271
  (Polychromatic418967fa.accept_17_4_3_16_1_9483 72 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 190 271 (accept_3_3 71 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 190 271 (Polychromatic418967fa.accept_11_4_3_7_1_828 70 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 190 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 190 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 190 271 (accept_3_3 68 190 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 190 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 67 190 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 190 271
  (Polychromatic418967fa.accept_7_3_1_5_1_44 66 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 190 271 (accept_3_3 65 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 190 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 64 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 190 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 190 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 190 271 (accept_3_3 62 190 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 190 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 190 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 190 271
  (Polychromatic418967fa.accept_7_4_1_5_1_540 60 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 190 271 (accept_3_3 59 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 190 271 (Polychromatic418967fa.accept_13_6_8_11_1_5398 58 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 190 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 190 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 190 271 (accept_3_3 56 190 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 190 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 55 190 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 190 271
  (Polychromatic418967fa.accept_11_10_3_7_1_2564 54 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 190 271 (accept_3_3 53 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 190 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 190 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 190 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 190 271 (accept_3_3 50 190 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 190 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 190 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 190 271
  (Polychromatic418967fa.accept_7_6_1_5_1_322 48 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 190 271 (accept_3_3 47 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 190 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 46 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 190 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 190 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 190 271 (accept_3_3 44 190 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 190 271 (Polychromatic418967fa.accept_11_10_3_7_1_2564 43 190 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 190 271
  (Polychromatic418967fa.accept_13_3_8_11_1_1906 42 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 190 271 (accept_3_3 41 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 190 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 190 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 190 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 190 271 (accept_3_3 38 190 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 190 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 190 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 190 271
  (Polychromatic418967fa.accept_13_10_8_11_1_1985 36 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 190 271 (accept_3_3 35 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 190 271 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 190 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 190 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 190 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 190 271 (accept_3_3 32 190 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 190 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 31
  190 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 190 271
  (Polychromatic418967fa.accept_13_4_8_11_1_1937 30 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 190 271 (accept_3_3 29 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 190 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 190 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 190 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 190 271 (accept_3_3 26 190 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 190 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 190 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 190 271
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 190 271 (accept_3_3 23 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 190 271 (Polychromatic418967fa.accept_13_9_8_11_1_725 22 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 190 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 190 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 190 271 (accept_3_3 20 190 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 190 271 (Polychromatic418967fa.accept_13_6_8_11_1_5398 19 190 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 190 271
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 190 271 (accept_3_3 17 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 190 271 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 190 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 190 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 190 271 (accept_3_3 14 190 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 190 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 190 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 190 271
  (Polychromatic418967fa.accept_21_12_1_19_1_4485 12 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 190 271 (accept_3_3 11 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 190 271 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 190 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 190 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 190 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 190 271 (accept_3_3 8 190 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 190 271 (Polychromatic418967fa.accept_15_7_10_1_1_1836
  7 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 190 271
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 190 271 (accept_3_3 5 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  190 271 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 190 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 190 271 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 190 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 190 271 (accept_3_3 2 190 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 190 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 190 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 190
  271)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 189 271 (Eq.refl
  Bool.true) (allA_succ_of_accept 82 189 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 189 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 189 271
  (Polychromatic418967fa.accept_13_3_7_11_1_1904 81 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 189 271 (accept_3_3 80 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 189 271 (Polychromatic418967fa.accept_13_1_7_11_1_702 79 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 189 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 189 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 189 271 (accept_3_3 77 189 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 189 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 189 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 189 271
  (Polychromatic418967fa.accept_10_5_9_1_1_187 75 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 189 271 (accept_3_3 74 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 189 271 (Polychromatic418967fa.accept_17_5_2_16_1_1294 73 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 189 271 (Polychromatic418967fa.accept_10_2_9_1_1_185 72 189 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 189 271 (accept_3_3 71 189 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 189 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 189 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 189 271
  (Polychromatic418967fa.accept_13_4_7_11_1_1981 69 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 189 271 (accept_3_3 68 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 189 271 (Polychromatic418967fa.accept_15_7_9_1_1_473 67 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 189 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 189 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 189 271 (accept_3_3 65 189 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 189 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 189 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 189 271
  (Polychromatic418967fa.accept_12_3_9_7_1_472 63 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 189 271 (accept_3_3 62 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 189 271 (Polychromatic418967fa.accept_13_9_7_11_1_1292 61 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 189 271 (Polychromatic418967fa.accept_16_12_13_15_1_1966 60 189 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 189 271 (accept_3_3 59 189 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 189 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 189 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 189 271
  (Polychromatic418967fa.accept_13_5_7_11_1_3470 57 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 189 271 (accept_3_3 56 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 189 271 (Polychromatic418967fa.accept_10_5_9_1_1_187 55 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 189 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 189 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 189 271 (accept_3_3 53 189 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 189 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 189 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 189 271
  (Polychromatic418967fa.accept_12_3_9_7_1_472 51 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 189 271 (accept_3_3 50 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 189 271 (Polychromatic418967fa.accept_31_18_3_23_1_16637 49 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 189 271 (Polychromatic418967fa.accept_10_8_9_1_1_189 48 189 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 189 271 (accept_3_3 47 189 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 189 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 189 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 189 271
  (Polychromatic418967fa.accept_10_5_9_1_1_187 45 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 189 271 (accept_3_3 44 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 189 271 (Polychromatic418967fa.accept_13_4_7_11_1_1981 43 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 189 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 189 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 189 271 (accept_3_3 41 189 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 189 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 189 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 189 271
  (Polychromatic418967fa.accept_12_3_9_7_1_472 39 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 189 271 (accept_3_3 38 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 189 271 (Polychromatic418967fa.accept_14_9_7_5_1_1105 37 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 189 271 (Polychromatic418967fa.accept_15_6_9_1_1_1823 36 189 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 189 271 (accept_3_3 35 189 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 189 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 189 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 189 271
  (Polychromatic418967fa.accept_23_10_5_18_1_6774 33 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 189 271 (accept_3_3 32 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 189 271 (Polychromatic418967fa.accept_11_9_2_7_1_1298 31 189 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 189 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 189 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 189 271 (accept_3_3 29 189 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 189 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 28
  189 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 189 271
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 189 271 (accept_3_3 26 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 189 271 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 189 271 (Polychromatic418967fa.accept_18_6_9_1_1_3769 24 189 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 189 271 (accept_3_3 23 189 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 189 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 189 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 189 271
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 21 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 189 271 (accept_3_3 20 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 189 271 (Polychromatic418967fa.accept_16_3_13_15_1_1913 19 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 189 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 189 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 189 271 (accept_3_3 17 189 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 189 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 189 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 189 271
  (Polychromatic418967fa.accept_10_5_9_1_1_187 15 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 189 271 (accept_3_3 14 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 189 271 (Polychromatic418967fa.accept_19_13_18_5_1_8619 13 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 189 271 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 189 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 189 271 (accept_3_3 11 189 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 189 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 189 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 189 271
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 189 271 (accept_3_3 8 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  189 271 (Polychromatic418967fa.accept_15_7_9_1_1_473 7 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 189 271 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 189 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 189 271 (accept_3_3 5 189 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 189 271 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 189 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 189 271
  (Polychromatic418967fa.accept_12_3_9_7_1_472 3 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 189 271 (accept_3_3 2 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  189 271 (Polychromatic418967fa.accept_13_1_7_11_1_702 1 189 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 189 271)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 84 188 271 (Eq.refl Bool.true) (allA_of_3_1 84 188 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 85 187 271 (Eq.refl Bool.true) (allA_succ_of_accept 84 187 271 (Polychromatic418967fa.accept_8_4_3_7_1_491
  84 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 187 271 (accept_3_3 83
  187 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 187 271
  (Polychromatic418967fa.accept_22_16_11_7_1_16636 82 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 187 271 (Polychromatic418967fa.accept_13_3_5_11_1_716 81 187 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 187 271 (accept_3_3 80 187 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 187 271 (Polychromatic418967fa.accept_19_3_16_5_1_7098 79 187
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 187 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 78 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 187 271 (accept_3_3 77 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 187 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 76 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 187 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 75 187 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 187 271 (accept_3_3 74 187 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 187 271 (Polychromatic418967fa.accept_24_1_19_7_1_6281 73 187 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 187 271
  (Polychromatic418967fa.accept_13_7_5_11_1_1927 72 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 187 271 (accept_3_3 71 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 187 271 (Polychromatic418967fa.accept_15_10_7_1_1_3686 70 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 187 271 (Polychromatic418967fa.accept_9_6_7_1_1_145 69 187 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 187 271 (accept_3_3 68 187 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 187 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 187 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 187 271
  (Polychromatic418967fa.accept_9_3_7_1_1_143 66 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 187 271 (accept_3_3 65 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 187 271 (Polychromatic418967fa.accept_10_4_7_1_1_471 64 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 187 271 (Polychromatic418967fa.accept_24_15_19_7_1_13255 63 187 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 187 271 (accept_3_3 62 187 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 187 271 (Polychromatic418967fa.accept_20_1_7_11_1_3673 61 187
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 187 271
  (Polychromatic418967fa.accept_8_4_3_7_1_491 60 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 187 271 (accept_3_3 59 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 187 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 187 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 57 187 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 187 271 (accept_3_3 56 187 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 187 271 (Polychromatic418967fa.accept_13_3_5_11_1_716 55 187 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 187 271
  (Polychromatic418967fa.accept_10_4_7_1_1_471 54 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 187 271 (accept_3_3 53 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 187 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 52 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 187 271 (Polychromatic418967fa.accept_9_6_7_1_1_145 51 187 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 187 271 (accept_3_3 50 187 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 187 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 187 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 187 271
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 187 271 (accept_3_3 47 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 187 271 (Polychromatic418967fa.accept_10_6_7_1_1_1297 46 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 187 271 (Polychromatic418967fa.accept_13_6_5_11_1_1971 45 187 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 187 271 (accept_3_3 44 187 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 187 271 (Polychromatic418967fa.accept_22_21_11_7_1_16635 43
  187 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 187 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 187 271 (accept_3_3 41 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 187 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 187 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 187 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 187 271 (accept_3_3 38 187 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 187 271 (Polychromatic418967fa.accept_22_15_11_7_1_2607 37 187 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 187 271
  (Polychromatic418967fa.accept_8_4_3_7_1_491 36 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 187 271 (accept_3_3 35 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 187 271 (Polychromatic418967fa.accept_10_4_7_1_1_471 34 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 187 271 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 187 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 187 271 (accept_3_3 32 187 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 187 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 187 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 187 271
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 187 271 (accept_3_3 29 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 187 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 187 271 (Polychromatic418967fa.accept_19_8_16_5_1_8583 27 187 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 187 271 (accept_3_3 26 187 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 187 271 (Polychromatic418967fa.accept_15_10_7_1_1_3686 25 187
  271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 187 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 187 271 (accept_3_3 23 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 187 271 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 187 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 187 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 187 271 (accept_3_3 20 187 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 187 271 (Polychromatic418967fa.accept_13_6_5_11_1_1971 19 187 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 187 271
  (Polychromatic418967fa.accept_20_18_7_11_1_3692 18 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 187 271 (accept_3_3 17 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 187 271 (Polychromatic418967fa.accept_10_6_7_1_1_1297 16 187 271 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 187 271 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 187 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 187 271 (accept_3_3 14 187 271
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 187 271 (Polychromatic418967fa.accept_9_4_7_1_1_379
  13 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 187 271
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 187 271 (accept_3_3 11 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 187 271 (Polychromatic418967fa.accept_15_10_7_1_1_3686 10 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 187 271 (Polychromatic418967fa.accept_15_9_7_1_1_1075 9 187 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 187 271 (accept_3_3 8 187 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 187 271 (Polychromatic418967fa.accept_13_7_5_11_1_1927 7 187 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 187 271
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 187 271 (accept_3_3 5 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  187 271 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 187 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 187 271 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 187 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 187 271 (accept_3_3 2 187 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 187 271 (Polychromatic418967fa.accept_16_1_11_15_1_498 1 187 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 187
  271))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 186 271
  (Eq.refl Bool.true) (allA_succ_of_accept 85 186 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 186 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 186 271
  (Polychromatic418967fa.accept_9_3_6_1_1_24 84 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 186 271 (accept_3_3 83 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 186 271 (Polychromatic418967fa.accept_10_2_6_1_1_1296 82 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 186 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 186 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 186 271 (accept_3_3 80 186 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 186 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 79 186 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 186 271
  (Polychromatic418967fa.accept_7_1_4_5_1_35 78 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 186 271 (accept_3_3 77 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 186 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 76 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 186 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 75 186 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 186 271 (accept_3_3 74 186 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 186 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 186 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 186 271
  (Polychromatic418967fa.accept_7_2_4_5_1_313 72 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 186 271 (accept_3_3 71 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 186 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 70 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 186 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 186 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 186 271 (accept_3_3 68 186 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 186 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 67 186 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 186 271
  (Polychromatic418967fa.accept_9_3_6_1_1_24 66 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 186 271 (accept_3_3 65 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 186 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 64 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 186 271 (Polychromatic418967fa.accept_15_3_6_1_1_1834 63 186 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 186 271 (accept_3_3 62 186 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 186 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 186 271
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 186 271
  (Polychromatic418967fa.accept_13_8_4_11_1_3469 60 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 186 271 (accept_3_3 59 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 186 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 58 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 186 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 186 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 186 271 (accept_3_3 56 186 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 186 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 55 186 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 186 271
  (Polychromatic418967fa.accept_13_2_4_11_1_2003 54 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 186 271 (accept_3_3 53 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 186 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 52 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 186 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 186 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 186 271 (accept_3_3 50 186 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 186 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 186 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 186 271
  (Polychromatic418967fa.accept_7_6_4_5_1_314 48 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 186 271 (accept_3_3 47 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 186 271 (Polychromatic418967fa.accept_13_7_4_11_1_1967 46 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 186 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 186 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 186 271 (accept_3_3 44 186 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 186 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 186 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 186 271
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 186 271 (accept_3_3 41 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 186 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 186 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 186 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 186 271 (accept_3_3 38 186 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 186 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 186 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 186 271
  (Polychromatic418967fa.accept_7_1_4_5_1_35 36 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 186 271 (accept_3_3 35 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 186 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 186 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 186 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 186 271 (accept_3_3 32 186 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 186 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 186 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 186 271
  (Polychromatic418967fa.accept_7_2_4_5_1_313 30 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 186 271 (accept_3_3 29 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 186 271 (Polychromatic418967fa.accept_13_2_4_11_1_2003 28 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 186 271 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 186 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 186 271 (accept_3_3 26 186 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 186 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 186 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 186 271
  (Polychromatic418967fa.accept_15_9_6_1_1_493 24 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 186 271 (accept_3_3 23 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 186 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 186 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 186 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 186 271 (accept_3_3 20 186 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 186 271 (Polychromatic418967fa.accept_13_6_4_11_1_282 19 186 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 186 271
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 18 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 186 271 (accept_3_3 17 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 186 271 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 186 271 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 186 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 186 271 (accept_3_3 14 186 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 186 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 186 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 186 271
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 186 271 (accept_3_3 11 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 186 271 (Polychromatic418967fa.accept_13_10_4_11_1_1969 10 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 186 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 186 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 186 271 (accept_3_3 8 186 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 186 271 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 186 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 186 271
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 186 271 (accept_3_3 5 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  186 271 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 186 271 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 186 271 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 186 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 186 271 (accept_3_3 2 186 271 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 186 271 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 186 271 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186
  271))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_271_segment_001)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


