-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch123
-- name    : Polychromatic418967fa_Branch123
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:12:46.649175+00:00
-- url     : https://prove2.me/theorems/37950592-ba23-43a6-9b88-ea62268c0d65
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_123 : allB 123 123 :=
  allB_succ' 2 122 123 (Eq.refl Bool.true) (allA_succ_of_accept 1 122 123 (accept_3_4 1 122 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 122 123)) (allB_succ' 3 121 123 (Eq.refl Bool.true) (allA_succ_of_accept 2 121 123
  (accept_3_5 2 121 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 121 123
  (Polychromatic418967fa.accept_9_1_4_6_1_5 1 121 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 121 123))) (allB_succ' 4 120 123 (Eq.refl Bool.true) (allA_succ_of_gcd 3 120 123 3 1 40 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 120 123
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 120 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 120 123 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 120 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 120 123)))) (allB_succ' 5 119 123 (Eq.refl Bool.true) (allA_succ_of_accept 4
  119 123 (accept_3_4 4 119 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 123
  (Polychromatic418967fa.accept_9_3_2_6_1_264 3 119 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 119 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 119 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 119 123 (accept_3_4 1 119 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 119 123))))) (allB_succ' 6 118 123 (Eq.refl Bool.true) (allA_succ_of_accept 5 118 123
  (accept_3_5 5 118 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 118 123
  (Polychromatic418967fa.accept_9_4_1_6_1_284 4 118 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 118 123 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 118 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 118 123 (accept_3_5 2 118 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 118 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 118 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118 123)))))) (allB_succ' 7 117 123 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 117 123 3 2 39 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 117 123 (Polychromatic418967fa.accept_10_5_7_3_1_561 5 117 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 123 (Polychromatic418967fa.accept_10_4_7_3_1_54 4 117 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 117 123 3 1 39 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 117 123
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 117 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 117 123 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 117 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 117 123))))))) (allB_succ' 8 116 123 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 116 123 (accept_3_4 7 116 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  116 123 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 116 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 116 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 116 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 116 123 (accept_3_4 4 116 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 116 123 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 116 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 116 123
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 116 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 116 123 (accept_3_4 1 116 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  123)))))))) (allB_succ' 9 115 123 (Eq.refl Bool.true) (allA_succ_of_accept 8 115 123 (accept_3_5 8 115 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 115 123 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 115 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 123
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 115 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 115 123 (accept_3_5 5 115 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  115 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 115 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 115 123 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 115 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 123 (accept_3_5 2 115 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 123 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 115 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115 123))))))))) (allB_succ' 10 114 123 (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 114 123 3 3 38 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 114 123 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 114 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 114 123 (Polychromatic418967fa.accept_10_7_4_3_1_560 7
  114 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114 123 3 2 38 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 114 123
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 114 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 114 123 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 114 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 114 123 3 1 38 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 114 123 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 114 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 123
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 114 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 114 123)))))))))) (allB_succ' 11 113 123 (Eq.refl Bool.true) (allA_succ_of_accept 10 113 123 (accept_3_4 10
  113 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 123
  (Polychromatic418967fa.accept_12_9_5_3_1_782 9 113 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 113 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 113 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 113 123 (accept_3_4 7 113 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 113 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 113 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 113 123 (Polychromatic418967fa.accept_7_5_1_4_1_122 5
  113 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 123 (accept_3_4 4 113
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 123
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 113 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 113 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 113 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 113 123 (accept_3_4 1 113 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 113 123))))))))))) (allB_succ' 12 112 123 (Eq.refl Bool.true) (allA_succ_of_accept 11 112 123
  (accept_3_5 11 112 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 112 123
  (Polychromatic418967fa.accept_9_1_4_6_1_5 10 112 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 112 123 (Polychromatic418967fa.accept_18_9_4_15_1_555 9 112 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 112 123 (accept_3_5 8 112 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 112 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 112 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 112 123 (Polychromatic418967fa.accept_12_6_4_3_1_361 6
  112 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 112 123 (accept_3_5 5 112
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 112 123
  (Polychromatic418967fa.accept_15_4_7_3_1_119 4 112 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 112 123 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 112 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 112 123 (accept_3_5 2 112 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 112 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 112 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112 123)))))))))))) (allB_succ' 13 111 123 (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 111 123 3 4 37 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 111 123 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 111 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 123 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 111 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 111 123 3 3 37 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 111 123
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 111 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 111 123 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 111 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 111 123 3 2 37 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 111 123 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 111 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 123
  (Polychromatic418967fa.accept_8_4_7_3_1_144 4 111 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 111 123 3 1 37 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 111 123 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 111 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 123 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 111 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111 123))))))))))))) (allB_succ' 14 110 123
  (Eq.refl Bool.true) (allA_succ_of_accept 13 110 123 (accept_3_4 13 110 123 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 110 123 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 110 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 110 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 110 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 110 123 (accept_3_4 10 110 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 110 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 9
  110 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 110 123
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 110 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 110 123 (accept_3_4 7 110 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  110 123 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 110 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 110 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 110 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 110 123 (accept_3_4 4 110 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 110 123 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 110 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 110 123
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 110 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 110 123 (accept_3_4 1 110 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  123)))))))))))))) (allB_succ' 15 109 123 (Eq.refl Bool.true) (allA_succ_of_accept 14 109 123 (accept_3_5 14 109 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 109 123 (Polychromatic418967fa.accept_9_4_1_6_1_284
  13 109 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 109 123
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 109 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 109 123 (accept_3_5 11 109 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 109 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 109 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 109 123 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 109 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 109 123 (accept_3_5 8 109 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 109 123 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 109 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 109 123
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 109 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 109 123 (accept_3_5 5 109 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  109 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 109 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 109 123 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 109 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 109 123 (accept_3_5 2 109 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 109 123 (Polychromatic418967fa.accept_11_1_10_2_1_58 1 109 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 109 123))))))))))))))) (allB_succ' 16 108 123 (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 108 123 3 5 36 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 108 123 (Polychromatic418967fa.accept_20_14_8_3_1_6011 14 108 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 108 123
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 108 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 108 123 3 4 36 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 108 123 (Polychromatic418967fa.accept_10_1_8_3_1_947 11 108 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 108 123 (Polychromatic418967fa.accept_13_10_4_6_1_3224 10 108
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 108 123 3 3 36 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 108 123
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 108 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 108 123 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 108 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 123 3 2 36 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 123 (Polychromatic418967fa.accept_10_5_8_3_1_229 5 108 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 108 123
  (Polychromatic418967fa.accept_11_4_9_2_1_259 4 108 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 108 123 3 1 36 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 108 123 (Polychromatic418967fa.accept_13_2_4_6_1_2356 2 108 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 108 123 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 108 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108 123)))))))))))))))) (allB_succ' 17 107 123
  (Eq.refl Bool.true) (allA_succ_of_accept 16 107 123 (accept_3_4 16 107 123 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 107 123 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 107 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 107 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 107 123 (accept_3_4 13 107 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 107 123 (Polychromatic418967fa.accept_7_5_2_4_1_126
  12 107 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 107 123
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 107 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 107 123 (accept_3_4 10 107 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  107 123 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 107 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 107 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 107 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 123 (accept_3_4 7 107 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 107 123 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 107 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 123
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 107 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 107 123 (accept_3_4 4 107 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  107 123 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 107 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 107 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 107 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 123 (accept_3_4 1 107 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 107 123))))))))))))))))) (allB_succ' 18 106 123 (Eq.refl Bool.true)
  (allA_succ_of_accept 17 106 123 (accept_3_5 17 106 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 106 123 (Polychromatic418967fa.accept_22_16_18_13_1_5986 16 106 123 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 106 123 (Polychromatic418967fa.accept_16_15_10_11_1_1727 15 106 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 106 123 (accept_3_5 14 106 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 106 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 13
  106 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 106 123
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 106 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 106 123 (accept_3_5 11 106 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 106 123 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 106 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 106 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 106 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 106 123 (accept_3_5 8 106 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 106 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 106 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 106 123
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 106 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 106 123 (accept_3_5 5 106 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  106 123 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 106 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 106 123 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 106 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 106 123 (accept_3_5 2 106 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 106 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 106 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106 123)))))))))))))))))) (allB_succ' 19 105 123
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 105 123 3 6 35 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 105 123 (Polychromatic418967fa.accept_10_7_5_3_1_542 17 105 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 123
  (Polychromatic418967fa.accept_13_3_1_6_1_509 16 105 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 105 123 3 5 35 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 105 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 105 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 123 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 105
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 105 123 3 4 35 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 105 123
  (Polychromatic418967fa.accept_12_11_9_3_1_792 11 105 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 105 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 105 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 105 123 3 3 35 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 105 123 (Polychromatic418967fa.accept_10_8_5_3_1_543 8 105 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 123
  (Polychromatic418967fa.accept_10_7_5_3_1_542 7 105 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 105 123 3 2 35 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 105 123 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 105 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 123 (Polychromatic418967fa.accept_11_4_6_2_1_51 4 105 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 105 123 3 1 35 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 105 123
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 105 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 123 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 105 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 105 123))))))))))))))))))) (allB_succ' 20 104 123 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 104 123 (accept_3_4 19 104 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 104 123 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 104 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 104 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 104 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 104 123 (accept_3_4 16 104 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 104 123 (Polychromatic418967fa.accept_17_15_2_4_1_2423 15 104 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 104 123
  (Polychromatic418967fa.accept_20_14_4_3_1_2006 14 104 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 104 123 (accept_3_4 13 104 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 104 123 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 104 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 104 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 104 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 104 123 (accept_3_4 10 104 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 104 123 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 104 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 104 123
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 104 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 104 123 (accept_3_4 7 104 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  104 123 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 104 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 104 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 104 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 104 123 (accept_3_4 4 104 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 104 123 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 104 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 104 123
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 104 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 104 123 (accept_3_4 1 104 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  123)))))))))))))))))))) (allB_succ' 21 103 123 (Eq.refl Bool.true) (allA_succ_of_accept 20 103 123 (accept_3_5 20 103
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 103 123 (Polychromatic418967fa.accept_9_1_4_6_1_5
  19 103 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 103 123
  (Polychromatic418967fa.accept_13_5_12_6_1_508 18 103 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 103 123 (accept_3_5 17 103 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 103 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 103 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 103 123 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 103 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 103 123 (accept_3_5 14 103 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 103 123 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 103 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 103 123
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 103 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 103 123 (accept_3_5 11 103 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 103 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 103 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 103 123 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 103 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 103 123 (accept_3_5 8 103 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 103 123 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 103 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 103 123
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 103 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 103 123 (accept_3_5 5 103 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  103 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 103 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 103 123 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 103 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 103 123 (accept_3_5 2 103 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 103 123 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 103 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 103 123))))))))))))))))))))) (allB_succ' 22 102 123
  (Eq.refl Bool.true) (allA_succ_of_gcd 21 102 123 3 7 34 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 102 123 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 102 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 102 123
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 102 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 123 3 6 34 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 102 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 102 123 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 102 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 102 123 3 5 34 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 102 123
  (Polychromatic418967fa.accept_9_5_3_6_1_269 14 102 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 102 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 102 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 123 3 4 34 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 123 (Polychromatic418967fa.accept_9_2_3_6_1_88 11
  102 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 102 123
  (Polychromatic418967fa.accept_9_1_3_6_1_70 10 102 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 102 123 3 3 34 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 102 123 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 102 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 123 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 102 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102 123 3 2 34 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 102 123
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 102 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 102 123 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 102 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 102 123 3 1 34 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 102 123 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 102 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 123
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 102 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 102 123)))))))))))))))))))))) (allB_succ' 23 101 123 (Eq.refl Bool.true) (allA_succ_of_accept 22 101 123
  (accept_3_4 22 101 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 123
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 101 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 101 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 101 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 101 123 (accept_3_4 19 101 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 101 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 101 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 101 123 (Polychromatic418967fa.accept_9_8_2_6_1_875
  17 101 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 123 (accept_3_4 16
  101 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 123
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 101 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 101 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 101 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 101 123 (accept_3_4 13 101 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 101 123 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 101 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 101 123
  (Polychromatic418967fa.accept_29_11_14_7_1_6013 11 101 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 101 123 (accept_3_4 10 101 123 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 101 123 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 101 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 101 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 101 123 (accept_3_4 7 101 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 101 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 6
  101 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 101 123
  (Polychromatic418967fa.accept_9_5_2_6_1_265 5 101 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 101 123 (accept_3_4 4 101 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  101 123 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 101 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 101 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 101 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 101 123 (accept_3_4 1 101 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 101 123))))))))))))))))))))))) (allB_succ' 24 100 123 (Eq.refl Bool.true)
  (allA_succ_of_accept 23 100 123 (accept_3_5 23 100 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 100 123 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 100 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 100 123 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 100 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 100 123 (accept_3_5 20 100 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 100 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 100 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 100 123
  (Polychromatic418967fa.accept_12_6_4_3_1_361 18 100 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 100 123 (accept_3_5 17 100 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 100 123 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 100 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 100 123 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 100 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 100 123 (accept_3_5 14 100 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 100 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 100 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 100 123
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 100 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 100 123 (accept_3_5 11 100 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 100 123 (Polychromatic418967fa.accept_11_10_1_2_1_1624 10 100 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 100 123 (Polychromatic418967fa.accept_14_9_2_11_1_780 9 100 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 100 123 (accept_3_5 8 100 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 100 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 100 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 100 123
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 100 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 100 123 (accept_3_5 5 100 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  100 123 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 100 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 100 123 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 100 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 100 123 (accept_3_5 2 100 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 100 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 100 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100 123)))))))))))))))))))))))) (allB_succ' 25 99 123
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 99 123 3 8 33 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 99 123 (Polychromatic418967fa.accept_15_8_9_3_1_1194 23 99 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 123
  (Polychromatic418967fa.accept_16_6_3_11_1_3751 22 99 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 99 123 3 7 33 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 99 123 (Polychromatic418967fa.accept_15_5_9_3_1_528 20 99 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 123 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 99 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 99 123 3 6 33 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 99 123
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 99 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 99 123 (Polychromatic418967fa.accept_10_6_9_3_1_935 16 99 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 99 123 3 5 33 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 99 123 (Polychromatic418967fa.accept_10_4_9_3_1_1907 14 99 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 123
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 13 99 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 99 123 3 4 33 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 99 123 (Polychromatic418967fa.accept_13_11_8_6_1_1023 11 99 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 123 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 99 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 99 123 3 3 33 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 99 123
  (Polychromatic418967fa.accept_15_8_9_3_1_1194 8 99 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 123 (Polychromatic418967fa.accept_16_7_3_11_1_3682 7 99 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 99 123 3 2 33 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 99 123 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 99 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 123
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 4 99 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 99 123 3 1 33 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 99 123 (Polychromatic418967fa.accept_13_2_8_6_1_2390 2 99 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 123 (Polychromatic418967fa.accept_13_1_8_6_1_1016 1 99 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99 123))))))))))))))))))))))))) (allB_succ' 26
  98 123 (Eq.refl Bool.true) (allA_succ_of_accept 25 98 123 (accept_3_4 25 98 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 98 123 (Polychromatic418967fa.accept_15_9_8_3_1_557 24 98 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 98 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 23
  98 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 98 123 (accept_3_4 22 98
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 98 123 (Polychromatic418967fa.accept_4_1_2_3_1_9
  21 98 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 98 123
  (Polychromatic418967fa.accept_9_2_8_6_1_79 20 98 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 98 123 (accept_3_4 19 98 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  98 123 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 98 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 98 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 98 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 123 (accept_3_4 16 98 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 123 (Polychromatic418967fa.accept_10_5_8_3_1_229 15 98 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 98 123
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 98 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 98 123 (accept_3_4 13 98 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  98 123 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 98 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 98 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 98 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 123 (accept_3_4 10 98 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 98 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 98 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 123
  (Polychromatic418967fa.accept_17_8_13_4_1_6012 8 98 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 98 123 (accept_3_4 7 98 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 98
  123 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 98 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 98 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 98 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 123 (accept_3_4 4 98 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 98 123 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 98 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 123 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 98
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 98 123 (accept_3_4 1 98 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98 123)))))))))))))))))))))))))) (allB_succ' 27 97 123 (Eq.refl
  Bool.true) (allA_succ_of_accept 26 97 123 (accept_3_5 26 97 123 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 97 123 (Polychromatic418967fa.accept_10_5_7_3_1_561 25 97 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 123 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 97 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 97 123 (accept_3_5 23 97 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 97 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 22
  97 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 97 123
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 97 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 97 123 (accept_3_5 20 97 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  97 123 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 97 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 97 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 97 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 97 123 (accept_3_5 17 97 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 97 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 97 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 97 123
  (Polychromatic418967fa.accept_10_5_7_3_1_561 15 97 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 97 123 (accept_3_5 14 97 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  97 123 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 97 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 97 123 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 97 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 97 123 (accept_3_5 11 97 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 97 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 97 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 97 123
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 97 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 97 123 (accept_3_5 8 97 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 97
  123 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 97 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 97 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 97 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 97 123 (accept_3_5 5 97 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 97 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 97 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 97 123 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 97
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 123 (accept_3_5 2 97 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 97 123 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 97
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97 123)))))))))))))))))))))))))))
  (allB_succ' 28 96 123 (Eq.refl Bool.true) (allA_succ_of_gcd 27 96 123 3 9 32 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 96 123
  (Polychromatic418967fa.accept_15_11_6_3_1_1192 26 96 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 96 123 (Polychromatic418967fa.accept_13_12_5_6_1_1050 25 96 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96 123 3 8 32 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 96 123 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 96 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 96 123
  (Polychromatic418967fa.accept_7_1_5_4_1_134 22 96 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 96 123 3 7 32 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 96 123 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 96 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 123 (Polychromatic418967fa.accept_10_9_6_3_1_545 19 96 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 123 3 6 32 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 123
  (Polychromatic418967fa.accept_10_7_6_3_1_927 17 96 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 96 123 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 96 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 96 123 3 5 32 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 96 123 (Polychromatic418967fa.accept_13_1_5_6_1_1048 14 96 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 123
  (Polychromatic418967fa.accept_7_6_5_4_1_297 13 96 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 96 123 3 4 32 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 96 123 (Polychromatic418967fa.accept_13_11_5_6_1_519 11 96 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 96 123 (Polychromatic418967fa.accept_13_10_5_6_1_1671 10 96
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 96 123 3 3 32 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 96 123
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 96 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 96 123 (Polychromatic418967fa.accept_10_7_6_3_1_927 7 96 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 123 3 2 32 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 123 (Polychromatic418967fa.accept_11_5_8_2_1_588 5 96 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96 123
  (Polychromatic418967fa.accept_13_4_5_6_1_3201 4 96 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 96 123 3 1 32 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 96 123 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 96 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 123 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 96 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96 123)))))))))))))))))))))))))))) (allB_succ'
  29 95 123 (Eq.refl Bool.true) (allA_succ_of_accept 28 95 123 (accept_3_4 28 95 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 95 123 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 95 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 95 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 26
  95 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 123 (accept_3_4 25 95
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 123
  (Polychromatic418967fa.accept_13_11_4_6_1_1006 24 95 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 95 123 (Polychromatic418967fa.accept_13_10_4_6_1_3224 23 95 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 95 123 (accept_3_4 22 95 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 95 123 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 95 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 95 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 20
  95 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 123 (accept_3_4 19 95
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 123
  (Polychromatic418967fa.accept_10_8_5_3_1_543 18 95 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 95 123 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 95 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 95 123 (accept_3_4 16 95 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 95 123 (Polychromatic418967fa.accept_13_2_4_6_1_2356 15 95 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 95 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 14
  95 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 123 (accept_3_4 13 95
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 123
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 95 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 95 123 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 95 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 95 123 (accept_3_4 10 95 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 95 123 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 95 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 95 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 95
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 123 (accept_3_4 7 95 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 123 (Polychromatic418967fa.accept_15_6_5_3_1_1988 6
  95 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 123
  (Polychromatic418967fa.accept_13_5_4_6_1_2371 5 95 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 123 (accept_3_4 4 95 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  123 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 95 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 95 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 123 (accept_3_4 1 95 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95 123))))))))))))))))))))))))))))) (allB_succ' 30 94 123 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 94 123 (accept_3_5 29 94 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  94 123 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 94 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 94 123 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 94 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 94 123 (accept_3_5 26 94 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 94 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 94 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 94 123
  (Polychromatic418967fa.accept_18_6_4_15_1_2276 24 94 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 94 123 (accept_3_5 23 94 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  94 123 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 94 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 94 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 94 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 94 123 (accept_3_5 20 94 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 94 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 94 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 94 123
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 94 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 94 123 (accept_3_5 17 94 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  94 123 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 94 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 94 123 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 94 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 94 123 (accept_3_5 14 94 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 94 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 94 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 94 123
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 94 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 94 123 (accept_3_5 11 94 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  94 123 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 94 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 94 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 94 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 94 123 (accept_3_5 8 94 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 94 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 94 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 94 123
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 94 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 94 123 (accept_3_5 5 94 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 94
  123 (Polychromatic418967fa.accept_11_4_6_2_1_51 4 94 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 94 123 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 94 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 123 (accept_3_5 2 94 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 94 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 94 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94 123)))))))))))))))))))))))))))))) (allB_succ' 31 93 123 (Eq.refl
  Bool.true) (allA_succ_of_gcd 30 93 123 3 10 31 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 93 123 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 93 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 123 (Polychromatic418967fa.accept_9_1_3_6_1_70 28
  93 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 93 123 3 9 31 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 93 123
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 93 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 123 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 93 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 93 123 3 8 31 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 93 123 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 93 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 123
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 93 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 93 123 3 7 31 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 93 123 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 93 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 123 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 93 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 93 123 3 6 31 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 93 123
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 93 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 93 123 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 93 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 93 123 3 5 31 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 93 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 93 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 123
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 93 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 93 123 3 4 31 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 93 123 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 93 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 93 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 93 123 3 3 31 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 93 123
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 93 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 123 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 93 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 93 123 3 2 31 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 93 123 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 93 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 123
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 93 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 93 123 3 1 31 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 93 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 93 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 123 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 93 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93 123)))))))))))))))))))))))))))))))
  (allB_succ' 32 92 123 (Eq.refl Bool.true) (allA_succ_of_accept 31 92 123 (accept_3_4 31 92 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 92 123 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 92 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 92 123
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 92 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 92 123 (accept_3_4 28 92 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  92 123 (Polychromatic418967fa.accept_15_12_2_3_1_1146 27 92 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 92 123 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 92 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 92 123 (accept_3_4 25 92 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 92 123 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 92 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 92 123
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 92 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 92 123 (accept_3_4 22 92 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  92 123 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 92 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 92 123 (Polychromatic418967fa.accept_11_9_4_2_1_600 20 92 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 92 123 (accept_3_4 19 92 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 92 123 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 92 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 92 123
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 92 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 92 123 (accept_3_4 16 92 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  92 123 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 92 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 92 123 (Polychromatic418967fa.accept_9_5_2_6_1_265 14 92 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 92 123 (accept_3_4 13 92 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 92 123 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 92 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 92 123
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 92 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 92 123 (accept_3_4 10 92 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  92 123 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 92 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 92 123 (Polychromatic418967fa.accept_9_8_2_6_1_875 8 92 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 92 123 (accept_3_4 7 92 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 92 123 (Polychromatic418967fa.accept_11_6_4_2_1_599 6 92 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 92 123
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 92 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 92 123 (accept_3_4 4 92 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 92
  123 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 92 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 92 123 (Polychromatic418967fa.accept_13_2_1_6_1_2365 2 92 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 123 (accept_3_4 1 92 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 92 123)))))))))))))))))))))))))))))))) (allB_succ' 33 91 123 (Eq.refl Bool.true)
  (allA_succ_of_accept 32 91 123 (accept_3_5 32 91 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  91 123 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 91 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 91 123 (Polychromatic418967fa.accept_9_3_1_6_1_86 30 91 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 91 123 (accept_3_5 29 91 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 91 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 91 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 91 123
  (Polychromatic418967fa.accept_17_10_6_4_1_2506 27 91 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 91 123 (accept_3_5 26 91 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  91 123 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 91 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 91 123 (Polychromatic418967fa.accept_14_10_7_11_1_3015 24 91 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 123 (accept_3_5 23 91 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 91 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 91 123
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 91 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 91 123 (accept_3_5 20 91 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  91 123 (Polychromatic418967fa.accept_15_4_1_3_1_1922 19 91 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 91 123 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 91 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 123 (accept_3_5 17 91 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 91 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 123
  (Polychromatic418967fa.accept_21_15_7_18_1_4452 15 91 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 91 123 (accept_3_5 14 91 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  91 123 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 91 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 91 123 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 91 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 123 (accept_3_5 11 91 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 91 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 123
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 91 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 91 123 (accept_3_5 8 91 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91
  123 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 91 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 91 123 (Polychromatic418967fa.accept_15_6_1_3_1_2852 6 91 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 123 (accept_3_5 5 91 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 91 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 91 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 123 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 91
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 123 (accept_3_5 2 91 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 123 (Polychromatic418967fa.accept_11_1_3_2_1_1090 1
  91 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91 123)))))))))))))))))))))))))))))))))
  (allB_succ' 34 90 123 (Eq.refl Bool.true) (allA_succ_of_gcd 33 90 123 3 11 30 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 90 123
  (Polychromatic418967fa.accept_12_8_6_3_1_366 32 90 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 90 123 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 90 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 123 3 10 30 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 90
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 90 123
  (Polychromatic418967fa.accept_12_4_6_3_1_332 28 90 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 90 123 3 9 30 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 90 123 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 90 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 90 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 90 123 3 8 30 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 123
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 90 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 90 123 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 90 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 90 123 3 7 30 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 90 123 (Polychromatic418967fa.accept_12_8_6_3_1_366 20 90 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 123
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 90 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 90 123 3 6 30 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 90 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 90 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 90 123 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 90 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 90 123 3 5 30 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 90 123
  (Polychromatic418967fa.accept_12_2_6_3_1_331 14 90 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 90 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 90 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 123 3 4 30 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 123 (Polychromatic418967fa.accept_19_11_14_9_1_4599 11 90
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 90 123
  (Polychromatic418967fa.accept_7_3_6_4_1_30 10 90 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 90 123 3 3 30 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 90 123 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 90 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 123 (Polychromatic418967fa.accept_13_7_12_6_1_1039 7 90 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 123 3 2 30 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90 123
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 90 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 90 123 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 90 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 90 123 3 1 30 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 90 123 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 90 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 123
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 90 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 90 123)))))))))))))))))))))))))))))))))) (allB_succ' 35 89 123 (Eq.refl Bool.true) (allA_succ_of_accept 34
  89 123 (accept_3_4 34 89 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 89 123
  (Polychromatic418967fa.accept_12_9_5_3_1_782 33 89 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 89 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 89 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 123 (accept_3_4 31 89 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 89 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 89 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 123 (Polychromatic418967fa.accept_7_1_5_4_1_134 29
  89 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 89 123 (accept_3_4 28 89
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 89 123
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 89 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 89 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 89 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 123 (accept_3_4 25 89 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 89 123 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 89 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 123 (Polychromatic418967fa.accept_7_2_5_4_1_115 23
  89 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 89 123 (accept_3_4 22 89
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 89 123 (Polychromatic418967fa.accept_9_3_8_6_1_80
  21 89 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 89 123
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 89 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 89 123 (accept_3_4 19 89 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  89 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 89 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 89 123 (Polychromatic418967fa.accept_13_4_11_6_1_1033 17 89 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 89 123 (accept_3_4 16 89 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 89 123 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 89 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 89 123
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 89 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 89 123 (accept_3_4 13 89 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  89 123 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 89 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 89 123 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 89 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 89 123 (accept_3_4 10 89 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 89 123 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 89 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 89 123
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 89 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 89 123 (accept_3_4 7 89 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 89
  123 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 89 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 89 123 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 89 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 89 123 (accept_3_4 4 89 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 89 123 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 89 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 89 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 89
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 123 (accept_3_4 1 89 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 89 123))))))))))))))))))))))))))))))))))) (allB_succ' 36 88 123
  (Eq.refl Bool.true) (allA_succ_of_accept 35 88 123 (accept_3_5 35 88 123 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 88 123 (Polychromatic418967fa.accept_20_14_8_3_1_6011 34 88 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 88 123 (Polychromatic418967fa.accept_17_16_3_4_1_6010 33 88
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 88 123 (accept_3_5 32 88 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 88 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 31
  88 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 88 123
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 88 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 88 123 (accept_3_5 29 88 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  88 123 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 88 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 88 123 (Polychromatic418967fa.accept_15_12_13_3_1_1915 27 88 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 88 123 (accept_3_5 26 88 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 88 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 88 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 88 123
  (Polychromatic418967fa.accept_15_9_13_3_1_535 24 88 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 88 123 (accept_3_5 23 88 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  88 123 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 88 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 88 123 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 88 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 88 123 (accept_3_5 20 88 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 88 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 88 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 88 123
  (Polychromatic418967fa.accept_12_6_4_3_1_361 18 88 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 88 123 (accept_3_5 17 88 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  88 123 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 88 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 88 123 (Polychromatic418967fa.accept_10_5_8_3_1_229 15 88 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 88 123 (accept_3_5 14 88 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 88 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 88 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 88 123
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 88 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 88 123 (accept_3_5 11 88 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  88 123 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 88 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 88 123 (Polychromatic418967fa.accept_13_9_10_6_1_1028 9 88 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 88 123 (accept_3_5 8 88 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 88 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 88 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 88 123
  (Polychromatic418967fa.accept_10_6_8_3_1_930 6 88 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 88 123 (accept_3_5 5 88 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 88
  123 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 88 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 88 123 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 88 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 88 123 (accept_3_5 2 88 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 88 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 88 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88 123)))))))))))))))))))))))))))))))))))) (allB_succ' 37 87 123
  (Eq.refl Bool.true) (allA_succ_of_gcd 36 87 123 3 12 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 87 123 (Polychromatic418967fa.accept_10_5_7_3_1_561 35 87 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 123
  (Polychromatic418967fa.accept_7_6_3_4_1_294 34 87 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 87 123 3 11 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 87 123 (Polychromatic418967fa.accept_15_2_12_3_1_1183 32 87 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 123 (Polychromatic418967fa.accept_16_15_7_11_1_3760 31 87
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 87 123 3 10 29 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 87 123
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 87 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 87 123 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 87 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 87 123 3 9 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 87 123 (Polychromatic418967fa.accept_10_6_7_3_1_547 26 87 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 123
  (Polychromatic418967fa.accept_10_5_7_3_1_561 25 87 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 87 123 3 8 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 87 123 (Polychromatic418967fa.accept_11_1_10_2_1_58 23 87 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 123 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 87 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 87 123 3 7 29 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 87 123
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 87 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 123 (Polychromatic418967fa.accept_16_3_7_11_1_1723 19 87 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 87 123 3 6 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 87 123 (Polychromatic418967fa.accept_13_4_9_6_1_2376 17 87 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 123
  (Polychromatic418967fa.accept_10_6_7_3_1_547 16 87 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 87 123 3 5 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 87 123 (Polychromatic418967fa.accept_10_4_7_3_1_54 14 87 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 123 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 87 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 87 123 3 4 29 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 87 123
  (Polychromatic418967fa.accept_21_11_3_18_1_3068 11 87 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 123 (Polychromatic418967fa.accept_13_10_9_6_1_1026 10 87 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 87 123 3 3 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 87 123 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 87 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 123
  (Polychromatic418967fa.accept_13_7_9_6_1_148 7 87 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 87 123 3 2 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 87 123 (Polychromatic418967fa.accept_10_5_7_3_1_561 5 87 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 123 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 87 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 87 123 3 1 29 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 87 123
  (Polychromatic418967fa.accept_13_2_9_6_1_501 2 87 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 87 123 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 87 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 87 123))))))))))))))))))))))))))))))))))))) (allB_succ' 38 86 123 (Eq.refl
  Bool.true) (allA_succ_of_accept 37 86 123 (accept_3_4 37 86 123 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 86 123 (Polychromatic418967fa.accept_15_6_11_3_1_1172 36 86 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 86 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 86 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 123 (accept_3_4 34 86 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 86 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 33
  86 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 123
  (Polychromatic418967fa.accept_19_13_10_9_1_5995 32 86 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 86 123 (accept_3_4 31 86 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  86 123 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 86 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 86 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 86 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 123 (accept_3_4 28 86 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 86 123 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 86 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 123
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 86 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 86 123 (accept_3_4 25 86 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  86 123 (Polychromatic418967fa.accept_13_11_8_6_1_1023 24 86 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 86 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 86 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 123 (accept_3_4 22 86 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 86 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 86 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 123
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 86 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 86 123 (accept_3_4 19 86 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 123 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 86 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 86 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 123 (accept_3_4 16 86 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 123 (Polychromatic418967fa.accept_11_4_9_2_1_259 15 86 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 123
  (Polychromatic418967fa.accept_13_1_8_6_1_1016 14 86 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 86 123 (accept_3_4 13 86 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  86 123 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 86 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 86 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 86 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 123 (accept_3_4 10 86 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 86 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 123
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 86 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 123 (accept_3_4 7 86 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  123 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 86 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 86 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 86 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 123 (accept_3_4 4 86 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 86 123 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 86 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 123 (Polychromatic418967fa.accept_9_2_5_6_1_536 2
  86 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 123 (accept_3_4 1 86 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86 123)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 85 123
  (Eq.refl Bool.true) (allA_succ_of_accept 38 85 123 (accept_3_5 38 85 123 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 85 123 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 85 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 123 (Polychromatic418967fa.accept_15_6_10_3_1_2844 36 85
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 85 123 (accept_3_5 35 85 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 85 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 34
  85 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 85 123
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 85 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 85 123 (accept_3_5 32 85 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  85 123 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 85 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 85 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 85 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 85 123 (accept_3_5 29 85 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 85 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 85 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 85 123
  (Polychromatic418967fa.accept_10_7_5_3_1_542 27 85 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 85 123 (accept_3_5 26 85 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  85 123 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 85 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 85 123 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 85 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 85 123 (accept_3_5 23 85 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 85 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 85 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 85 123
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 85 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 85 123 (accept_3_5 20 85 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  85 123 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 85 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 85 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 85 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 123 (accept_3_5 17 85 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 85 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 85 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 85 123
  (Polychromatic418967fa.accept_20_15_5_3_1_1953 15 85 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 85 123 (accept_3_5 14 85 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  85 123 (Polychromatic418967fa.accept_15_13_10_3_1_1952 13 85 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 85 123 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 85 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 85 123 (accept_3_5 11 85 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 85 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 85 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 85 123
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 85 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 85 123 (accept_3_5 8 85 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 85
  123 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 85 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 85 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 85 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 85 123 (accept_3_5 5 85 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 85 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 85 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 85 123 (Polychromatic418967fa.accept_7_3_1_4_1_121 3
  85 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 123 (accept_3_5 2 85 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 123 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 85
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  123))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 84 123 (Eq.refl Bool.true) (allA_succ_of_gcd 39 84 123 3 13
  28 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 84 123
  (Polychromatic418967fa.accept_9_2_3_6_1_88 38 84 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 84 123 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 84 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84 123 3 12 28 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 84 123 (Polychromatic418967fa.accept_9_8_3_6_1_533 35
  84 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 84 123
  (Polychromatic418967fa.accept_9_7_3_6_1_270 34 84 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 84 123 3 11 28 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 84 123 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 84 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 123 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 84 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 123 3 10 28 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 123
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 84 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 84 123 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 84 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 84 123 3 9 28 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 84 123 (Polychromatic418967fa.accept_9_8_3_6_1_533 26 84 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 123
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 84 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 84 123 3 8 28 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 84 123 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 84 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 84 123 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 84 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 84 123 3 7 28 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 84 123
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 84 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 84 123 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 84 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 123 3 6 28 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 123 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 84 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 84 123
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 84 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 84 123 3 5 28 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 84 123 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 84 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 123 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 84 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 123 3 4 28 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 123
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 84 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 84 123 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 84 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 84 123 3 3 28 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 84 123 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 84 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 123
  (Polychromatic418967fa.accept_8_7_4_3_1_156 7 84 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 84 123 3 2 28 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 84 123 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 84 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84 123 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 84 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 84 123 3 1 28 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 84 123
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 84 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 84 123 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 84 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 84 123)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 83 123
  (Eq.refl Bool.true) (allA_succ_of_accept 40 83 123 (accept_3_4 40 83 123 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 83 123 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 83 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 83 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 83 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 123 (accept_3_4 37 83 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 123 (Polychromatic418967fa.accept_13_10_5_6_1_1671
  36 83 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 123
  (Polychromatic418967fa.accept_9_8_2_6_1_875 35 83 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 123 (accept_3_4 34 83 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 123 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 83 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 83 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 123 (accept_3_4 31 83 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 123 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 83 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 123
  (Polychromatic418967fa.accept_13_3_5_6_1_3192 29 83 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 123 (accept_3_4 28 83 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 123 (Polychromatic418967fa.accept_13_1_5_6_1_1048 27 83 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 83 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 123 (accept_3_4 25 83 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 123 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 83 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 123
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 83 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 123 (accept_3_4 22 83 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 123 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 83 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 83 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 123 (accept_3_4 19 83 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 123 (Polychromatic418967fa.accept_22_18_17_13_1_2923 18 83 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 123
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 83 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 123 (accept_3_4 16 83 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 123 (Polychromatic418967fa.accept_11_4_6_2_1_51 15 83 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 83 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 123 (accept_3_4 13 83 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 123 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 83 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 123
  (Polychromatic418967fa.accept_13_11_5_6_1_519 11 83 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 123 (accept_3_4 10 83 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 123 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 83 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 83 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 123 (accept_3_4 7 83 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 123 (Polychromatic418967fa.accept_16_6_3_11_1_3751 6 83 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 123
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 83 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 123 (accept_3_4 4 83 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  123 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 83 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 83 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 123 (accept_3_4 1 83 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 123))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 82 123 (Eq.refl Bool.true)
  (allA_succ_of_gcd 41 82 123 41 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 40 82 123 (Polychromatic418967fa.accept_9_4_1_6_1_284 40 82 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 82 123 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 82 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 82 123 (accept_3_5 38 82 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 82 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 37
  82 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 82 123
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 82 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 82 123 (accept_3_5 35 82 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  82 123 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 82 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 82 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 82 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 82 123 (accept_3_5 32 82 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 82 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 82 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 82 123
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 82 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 82 123 (accept_3_5 29 82 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  82 123 (Polychromatic418967fa.accept_13_2_4_6_1_2356 28 82 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 82 123 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 82 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 82 123 (accept_3_5 26 82 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 82 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 82 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 82 123
  (Polychromatic418967fa.accept_13_11_4_6_1_1006 24 82 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 82 123 (accept_3_5 23 82 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  82 123 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 82 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 82 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 82 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 82 123 (accept_3_5 20 82 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 82 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 82 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 82 123
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 82 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 82 123 (accept_3_5 17 82 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  82 123 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 82 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 82 123 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 82 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 82 123 (accept_3_5 14 82 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 82 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 82 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 82 123
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 82 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 82 123 (accept_3_5 11 82 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  82 123 (Polychromatic418967fa.accept_13_10_4_6_1_3224 10 82 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 82 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 82 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 82 123 (accept_3_5 8 82 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 82 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 82 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 82 123
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 82 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 82 123 (accept_3_5 5 82 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 82
  123 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 82 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 82 123 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 82 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 123 (accept_3_5 2 82 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 82 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 82 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82 123)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 81
  123 (Eq.refl Bool.true) (allA_succ_of_gcd 42 81 123 3 14 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 81 123 (Polychromatic418967fa.accept_12_5_9_3_1_85 41 81 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 123
  (Polychromatic418967fa.accept_13_1_3_6_1_158 40 81 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 81 123 3 13 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 81 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 81 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 123 (Polychromatic418967fa.accept_12_1_9_3_1_370 37 81 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 81 123 3 12 27 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 81 123
  (Polychromatic418967fa.accept_12_11_9_3_1_792 35 81 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 81 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 81 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 81 123 3 11 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 81 123 (Polychromatic418967fa.accept_10_2_1_3_1_233 32
  81 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 123
  (Polychromatic418967fa.accept_11_9_4_2_1_600 31 81 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 81 123 3 10 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 81 123 (Polychromatic418967fa.accept_12_5_9_3_1_85 29 81 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 123 (Polychromatic418967fa.accept_10_8_1_3_1_1374 28 81 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 81 123 3 9 27 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 81 123
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 81 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 81 123 (Polychromatic418967fa.accept_12_1_9_3_1_370 25 81 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 81 123 3 8 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 81 123 (Polychromatic418967fa.accept_12_11_9_3_1_792 23 81 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 123
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 81 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 81 123 3 7 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 81 123 (Polychromatic418967fa.accept_11_9_4_2_1_600 20 81 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 123 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 81 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 81 123 3 6 27 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 81 123
  (Polychromatic418967fa.accept_11_6_4_2_1_599 17 81 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 81 123 (Polychromatic418967fa.accept_15_1_6_3_1_2827 16 81 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 81 123 3 5 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 81 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 81 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 123
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 81 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 81 123 3 4 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 81 123 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 81 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 81 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 81 123 3 3 27 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 81 123
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 8 81 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 81 123 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 81 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 81 123 3 2 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 81 123 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 81 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 123
  (Polychromatic418967fa.accept_18_4_9_15_1_3383 4 81 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 81 123 3 1 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 81 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 81 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 123 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 81 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  123))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 80 123 (Eq.refl Bool.true) (allA_succ_of_accept 43 80
  123 (accept_3_4 43 80 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 80 123
  (Polychromatic418967fa.accept_12_6_8_3_1_82 42 80 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 80 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 80 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 80 123 (accept_3_4 40 80 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 80 123 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 80 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 123 (Polychromatic418967fa.accept_9_2_8_6_1_79 38
  80 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 80 123 (accept_3_4 37 80
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 80 123
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 80 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 80 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 80 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 80 123 (accept_3_4 34 80 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 80 123 (Polychromatic418967fa.accept_19_14_4_9_1_6009 33 80 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 80 123
  (Polychromatic418967fa.accept_9_5_8_6_1_281 32 80 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 80 123 (accept_3_4 31 80 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  80 123 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 80 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 80 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 80 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 123 (accept_3_4 28 80 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 123 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 80 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 123
  (Polychromatic418967fa.accept_17_9_12_4_1_3468 26 80 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 80 123 (accept_3_4 25 80 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  80 123 (Polychromatic418967fa.accept_15_9_5_3_1_554 24 80 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 80 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 80 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 123 (accept_3_4 22 80 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 80 123 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 80 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 80 123
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 80 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 80 123 (accept_3_4 19 80 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  80 123 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 80 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 80 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 80 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 123 (accept_3_4 16 80 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 80 123 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 80 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 80 123
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 80 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 80 123 (accept_3_4 13 80 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  80 123 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 80 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 80 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 80 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 80 123 (accept_3_4 10 80 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 80 123 (Polychromatic418967fa.accept_13_9_2_6_1_514 9 80 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 123
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 80 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 80 123 (accept_3_4 7 80 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80
  123 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 80 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 80 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 80 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 80 123 (accept_3_4 4 80 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 80 123 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 80 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 123 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 80
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 80 123 (accept_3_4 1 80 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80 123)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45
  79 123 (Eq.refl Bool.true) (allA_succ_of_accept 44 79 123 (accept_3_5 44 79 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 79 123 (Polychromatic418967fa.accept_24_19_7_3_1_6008 43 79 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 123
  (Polychromatic418967fa.accept_13_3_1_6_1_509 42 79 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 79 123 (accept_3_5 41 79 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  79 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 79 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 79 123 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 79 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 123 (accept_3_5 38 79 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 123 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 79 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 123
  (Polychromatic418967fa.accept_8_4_7_3_1_144 36 79 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 123 (accept_3_5 35 79 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 79 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 123 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 79 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 123 (accept_3_5 32 79 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 123 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 79 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 123
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 79 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 123 (accept_3_5 29 79 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 79 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 123 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 79 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 123 (accept_3_5 26 79 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 123 (Polychromatic418967fa.accept_19_6_3_9_1_3332 25 79 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 123
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 79 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 123 (accept_3_5 23 79 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 79 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 123 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 79 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 123 (accept_3_5 20 79 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 123 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 79 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 123
  (Polychromatic418967fa.accept_13_5_1_6_1_2367 18 79 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 123 (accept_3_5 17 79 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 79 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 123 (Polychromatic418967fa.accept_13_2_1_6_1_2365 15 79 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 123 (accept_3_5 14 79 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 123 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 79 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 123
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 79 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 123 (accept_3_5 11 79 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 79 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 123 (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 79 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 123 (accept_3_5 8 79 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 123 (Polychromatic418967fa.accept_13_7_1_6_1_3287 7 79 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 123
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 79 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 123 (accept_3_5 5 79 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  123 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 79 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 79 123 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 79 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 123 (accept_3_5 2 79 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 123 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 79 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79 123))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46
  78 123 (Eq.refl Bool.true) (allA_succ_of_gcd 45 78 123 3 15 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 78 123 (Polychromatic418967fa.accept_12_8_6_3_1_366 44 78 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 123
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 43 78 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 78 123 3 14 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 78 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 78 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 78 123 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 78 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 78 123 3 13 26 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 78 123
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 78 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 78 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 78 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 123 3 12 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 123 (Polychromatic418967fa.accept_10_5_8_3_1_229 35
  78 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 78 123
  (Polychromatic418967fa.accept_12_10_6_3_1_786 34 78 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 78 123 3 11 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 78 123 (Polychromatic418967fa.accept_11_10_1_2_1_1624 32 78 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 123 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 78 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 123 3 10 26 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 123
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 78 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 78 123 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 78 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 78 123 3 9 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 78 123 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 78 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 123
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 78 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 123 3 8 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 78 123 (Polychromatic418967fa.accept_17_6_10_4_1_6007 23 78 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 78 123 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 78 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 78 123 3 7 26 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 78 123
  (Polychromatic418967fa.accept_12_8_6_3_1_366 20 78 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 78 123 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 78 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 123 3 6 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 78 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 78 123
  (Polychromatic418967fa.accept_10_6_8_3_1_930 16 78 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 78 123 3 5 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 78 123 (Polychromatic418967fa.accept_11_3_1_2_1_1063 14 78 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 78 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 123 3 4 26 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 123
  (Polychromatic418967fa.accept_10_1_8_3_1_947 11 78 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 78 123 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 78 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 78 123 3 3 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 78 123 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 78 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 123
  (Polychromatic418967fa.accept_19_7_2_9_1_6006 7 78 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 78 123 3 2 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 78 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 78 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78 123 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 78 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 78 123 3 1 26 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 78 123
  (Polychromatic418967fa.accept_12_2_6_3_1_331 2 78 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 78 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 78 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 78 123)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 77 123
  (Eq.refl Bool.true) (allA_succ_of_accept 46 77 123 (accept_3_4 46 77 123 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 77 123 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 77 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 77 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 77 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 123 (accept_3_4 43 77 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 42
  77 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 123
  (Polychromatic418967fa.accept_13_2_12_6_1_2394 41 77 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 123 (accept_3_4 40 77 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 123 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 77 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 77 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 123 (accept_3_4 37 77 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 123 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 77 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 123
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 77 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 123 (accept_3_4 34 77 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 123 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 77 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 77 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 123 (accept_3_4 31 77 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 77 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 123
  (Polychromatic418967fa.accept_9_2_5_6_1_536 29 77 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 123 (accept_3_4 28 77 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 123 (Polychromatic418967fa.accept_15_12_2_3_1_1146 27 77 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 77 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 123 (accept_3_4 25 77 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 123 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 77 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 123
  (Polychromatic418967fa.accept_13_10_12_6_1_991 23 77 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 123 (accept_3_4 22 77 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 123 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 77 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 77 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 123 (accept_3_4 19 77 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 77 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 123
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 77 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 123 (accept_3_4 16 77 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 123 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 77 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 77 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 123 (accept_3_4 13 77 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 123 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 77 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 123
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 77 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 123 (accept_3_4 10 77 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 123 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 77 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 77 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 123 (accept_3_4 7 77 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 77 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 123
  (Polychromatic418967fa.accept_10_5_7_3_1_561 5 77 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 123 (accept_3_4 4 77 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  123 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 77 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 77 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 123 (accept_3_4 1 77 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 123))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 76 123 (Eq.refl Bool.true)
  (allA_succ_of_accept 47 76 123 (accept_3_5 47 76 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  76 123 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 76 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 76 123 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 76 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 76 123 (accept_3_5 44 76 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 76 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 76 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 76 123
  (Polychromatic418967fa.accept_12_6_4_3_1_361 42 76 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 76 123 (accept_3_5 41 76 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  76 123 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 76 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 76 123 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 76 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 76 123 (accept_3_5 38 76 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 76 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 76 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 76 123
  (Polychromatic418967fa.accept_15_6_1_3_1_2852 36 76 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 76 123 (accept_3_5 35 76 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  76 123 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 76 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 76 123 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 76 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 76 123 (accept_3_5 32 76 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 76 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 76 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 76 123
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 76 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 76 123 (accept_3_5 29 76 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  76 123 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 76 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 76 123 (Polychromatic418967fa.accept_10_7_6_3_1_927 27 76 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 76 123 (accept_3_5 26 76 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 76 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 76 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 76 123
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 76 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 76 123 (accept_3_5 23 76 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  76 123 (Polychromatic418967fa.accept_23_22_7_8_1_6005 22 76 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 76 123 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 76 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 76 123 (accept_3_5 20 76 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 76 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 76 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 76 123
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 76 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 76 123 (accept_3_5 17 76 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  76 123 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 76 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 76 123 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 76 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 76 123 (accept_3_5 14 76 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 76 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 76 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 76 123
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 76 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 76 123 (accept_3_5 11 76 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  76 123 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 76 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 76 123 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 76 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 76 123 (accept_3_5 8 76 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 76 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 76 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 76 123
  (Polychromatic418967fa.accept_12_6_4_3_1_361 6 76 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 76 123 (accept_3_5 5 76 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 76
  123 (Polychromatic418967fa.accept_13_4_11_6_1_1033 4 76 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 76 123 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 76 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 123 (accept_3_5 2 76 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 76 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 76 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76 123))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 49 75 123 (Eq.refl Bool.true) (allA_succ_of_gcd 48 75 123 3 16 25 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 75 123
  (Polychromatic418967fa.accept_9_2_3_6_1_88 47 75 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 75 123 (Polychromatic418967fa.accept_9_1_3_6_1_70 46 75 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75 123 3 15 25 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 75 123 (Polychromatic418967fa.accept_7_2_5_4_1_115 44
  75 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 123
  (Polychromatic418967fa.accept_7_1_5_4_1_134 43 75 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 75 123 3 14 25 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 75 123 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 75 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 123 (Polychromatic418967fa.accept_9_4_3_6_1_532 40 75 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 75 123 3 13 25 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 75 123
  (Polychromatic418967fa.accept_9_2_3_6_1_88 38 75 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 75 123 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 75 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 75 123 3 12 25 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 75 123 (Polychromatic418967fa.accept_9_8_3_6_1_533 35
  75 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 123
  (Polychromatic418967fa.accept_7_6_5_4_1_297 34 75 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 75 123 3 11 25 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 75 123 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 75 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 123 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 75 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 75 123 3 10 25 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 75 123
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 75 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 75 123 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 75 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 75 123 3 9 25 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 75 123 (Polychromatic418967fa.accept_9_8_3_6_1_533 26 75 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 123
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 75 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 75 123 3 8 25 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 75 123 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 75 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 123 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 75 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 75 123 3 7 25 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 75 123
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 75 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 75 123 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 75 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 75 123 3 6 25 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 75 123 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 75 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 123
  (Polychromatic418967fa.accept_7_2_5_4_1_115 16 75 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 75 123 3 5 25 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 75 123 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 75 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 123 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 75 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 75 123 3 4 25 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 75 123
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 75 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 75 123 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 75 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 75 123 3 3 25 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 75 123 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 75 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 123
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 75 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 75 123 3 2 25 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 75 123 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 75 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 123 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 75 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 75 123 3 1 25 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 75 123
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 75 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 75 123 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 75 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 75 123))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 74
  123 (Eq.refl Bool.true) (allA_succ_of_accept 49 74 123 (accept_3_4 49 74 123 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 74 123 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 74 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 74 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 74 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 123 (accept_3_4 46 74 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 74 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 45
  74 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 123
  (Polychromatic418967fa.accept_9_8_2_6_1_875 44 74 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 74 123 (accept_3_4 43 74 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  74 123 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 74 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 74 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 74 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 123 (accept_3_4 40 74 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 74 123 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 74 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 123
  (Polychromatic418967fa.accept_11_5_8_2_1_588 38 74 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 74 123 (accept_3_4 37 74 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  74 123 (Polychromatic418967fa.accept_13_10_9_6_1_1026 36 74 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 74 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 74 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 123 (accept_3_4 34 74 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 74 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 74 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 123
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 74 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 74 123 (accept_3_4 31 74 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  74 123 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 74 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 74 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 74 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 123 (accept_3_4 28 74 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 74 123 (Polychromatic418967fa.accept_10_7_4_3_1_560 27 74 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 123
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 74 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 74 123 (accept_3_4 25 74 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  74 123 (Polychromatic418967fa.accept_20_4_14_3_1_3181 24 74 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 74 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 74 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 123 (accept_3_4 22 74 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 74 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 74 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 123
  (Polychromatic418967fa.accept_13_7_9_6_1_148 20 74 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 74 123 (accept_3_4 19 74 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  74 123 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 74 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 74 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 74 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 123 (accept_3_4 16 74 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 74 123 (Polychromatic418967fa.accept_13_2_9_6_1_501 15 74 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 123
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 74 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 74 123 (accept_3_4 13 74 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  74 123 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 74 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 74 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 74 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 123 (accept_3_4 10 74 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 74 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 74 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 123
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 74 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 74 123 (accept_3_4 7 74 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74
  123 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 74 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 74 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 74 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 123 (accept_3_4 4 74 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 74 123 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 74 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 123 (Polychromatic418967fa.accept_13_2_9_6_1_501 2
  74 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 123 (accept_3_4 1 74 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74 123))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 51 73 123 (Eq.refl Bool.true) (allA_succ_of_accept 50 73 123 (accept_3_5 50 73 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 123 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 73 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 123
  (Polychromatic418967fa.accept_7_6_3_4_1_294 48 73 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 123 (accept_3_5 47 73 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 73 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 123 (Polychromatic418967fa.accept_12_9_1_3_1_350 45 73 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 123 (accept_3_5 44 73 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 123 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 73 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 123
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 73 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 123 (accept_3_5 41 73 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 73 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 123 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 73 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 123 (accept_3_5 38 73 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 123 (Polychromatic418967fa.accept_13_11_8_6_1_1023 37 73 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 123
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 73 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 123 (accept_3_5 35 73 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 73 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 123 (Polychromatic418967fa.accept_12_9_1_3_1_350 33 73 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 123 (accept_3_5 32 73 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 123 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 73 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 123
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 73 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 123 (accept_3_5 29 73 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 73 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 123 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 73 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 123 (accept_3_5 26 73 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 123 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 73 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 123
  (Polychromatic418967fa.accept_13_11_8_6_1_1023 24 73 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 123 (accept_3_5 23 73 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 73 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 123 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 73 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 123 (accept_3_5 20 73 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 123 (Polychromatic418967fa.accept_22_19_7_13_1_6004 19 73 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 123
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 73 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 123 (accept_3_5 17 73 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 73 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 123 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 73 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 123 (accept_3_5 14 73 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 123 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 73 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 123
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 73 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 123 (accept_3_5 11 73 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 73 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 123 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 73 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 123 (accept_3_5 8 73 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 123 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 73 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 123
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 73 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 123 (accept_3_5 5 73 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  123 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 73 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 123 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 73 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 123 (accept_3_5 2 73 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 123 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 73 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73 123)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 52 72 123 (Eq.refl Bool.true) (allA_succ_of_gcd 51 72 123 3 17 24 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 72 123
  (Polychromatic418967fa.accept_20_10_12_3_1_6003 50 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 72 123 (Polychromatic418967fa.accept_19_11_15_9_1_6002 49 72 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 123 3 16 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 123 (Polychromatic418967fa.accept_7_5_2_4_1_126 47
  72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 72 123
  (Polychromatic418967fa.accept_21_4_9_18_1_6001 46 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 72 123 3 15 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 72 123 (Polychromatic418967fa.accept_16_12_8_11_1_2695 44 72 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 123 (Polychromatic418967fa.accept_13_4_7_6_1_2359 43 72 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72 123 3 14 24 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 123
  (Polychromatic418967fa.accept_7_6_2_4_1_291 41 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 123 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 72 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 72 123 3 13 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 72 123 (Polychromatic418967fa.accept_13_12_7_6_1_1015
  38 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 123
  (Polychromatic418967fa.accept_11_4_6_2_1_51 37 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 72 123 3 12 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 72 123 (Polychromatic418967fa.accept_10_5_2_3_1_239 35 72 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 72 123 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 72 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 72 123 3 11 24 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 72 123
  (Polychromatic418967fa.accept_15_2_12_3_1_1183 32 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 72 123 (Polychromatic418967fa.accept_10_1_2_3_1_1910 31 72 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 123 3 10 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 123 (Polychromatic418967fa.accept_16_13_8_11_1_4785
  29 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 72 123
  (Polychromatic418967fa.accept_15_13_12_3_1_1180 28 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 72 123 3 9 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 72 123 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 72 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 123 (Polychromatic418967fa.accept_10_5_2_3_1_239 25 72 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 123 3 8 24 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 123
  (Polychromatic418967fa.accept_14_9_2_11_1_780 23 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 123 (Polychromatic418967fa.accept_13_9_7_6_1_1673 22 72 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 72 123 3 7 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 72 123 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 72 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 123
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 72 123 3 6 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 72 123 (Polychromatic418967fa.accept_13_4_7_6_1_2359 17 72 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 72 123 (Polychromatic418967fa.accept_22_16_6_13_1_6000 16 72
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 72 123 3 5 24 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 72 123
  (Polychromatic418967fa.accept_13_1_7_6_1_142 14 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 72 123 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 72 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 123 3 4 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 123 (Polychromatic418967fa.accept_10_1_2_3_1_1910 11 72 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 72 123
  (Polychromatic418967fa.accept_19_10_15_9_1_396 10 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 72 123 3 3 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 72 123 (Polychromatic418967fa.accept_15_8_12_3_1_1912 8 72 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 123 (Polychromatic418967fa.accept_15_7_12_3_1_1137 7 72 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 123 3 2 24 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 123
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 123 (Polychromatic418967fa.accept_11_4_6_2_1_51 4 72 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 72 123 3 1 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 72 123 (Polychromatic418967fa.accept_15_2_12_3_1_1183 2 72 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 123
  (Polychromatic418967fa.accept_10_1_2_3_1_1910 1 72 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 72 123)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 71 123 (Eq.refl Bool.true)
  (allA_succ_of_accept 52 71 123 (accept_3_4 52 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 123 (Polychromatic418967fa.accept_15_6_11_3_1_1172 51 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 71 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 123 (accept_3_4 49 71 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 123 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 71 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 123
  (Polychromatic418967fa.accept_7_5_1_4_1_122 47 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 123 (accept_3_4 46 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 123 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 71 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 123 (accept_3_4 43 71 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 123 (Polychromatic418967fa.accept_10_2_1_3_1_233 42 71 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 123
  (Polychromatic418967fa.accept_9_5_8_6_1_281 41 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 123 (accept_3_4 40 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 123 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 71 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 123 (accept_3_4 37 71 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 123 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 71 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 123
  (Polychromatic418967fa.accept_16_3_7_11_1_1723 35 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 123 (accept_3_4 34 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 123 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 71 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 123 (accept_3_4 31 71 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 123 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 71 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 123
  (Polychromatic418967fa.accept_9_2_8_6_1_79 29 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 123 (accept_3_4 28 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 123 (Polychromatic418967fa.accept_18_9_17_15_1_2267 27 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 71 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 123 (accept_3_4 25 71 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 123 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 71 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 123
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 123 (accept_3_4 22 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 123 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 71 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 123 (accept_3_4 19 71 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 123 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 71 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 123
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 123 (accept_3_4 16 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 123 (Polychromatic418967fa.accept_16_15_7_11_1_3760 15 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 71 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 123 (accept_3_4 13 71 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 123 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 71 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 123
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 123 (accept_3_4 10 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 123 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 71 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 123 (accept_3_4 7 71 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 123 (Polychromatic418967fa.accept_15_6_11_3_1_1172 6 71 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 123
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 123 (accept_3_4 4 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  123 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 71 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 71 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 123 (accept_3_4 1 71 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 123))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 70 123 (Eq.refl
  Bool.true) (allA_succ_of_accept 53 70 123 (accept_3_5 53 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 70 123 (Polychromatic418967fa.accept_15_7_10_3_1_2891 52 70 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 70 123 (Polychromatic418967fa.accept_13_12_5_6_1_1050 51 70
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 70 123 (accept_3_5 50 70 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 70 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 49
  70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 70 123
  (Polychromatic418967fa.accept_9_3_7_6_1_76 48 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 70 123 (accept_3_5 47 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  70 123 (Polychromatic418967fa.accept_9_1_7_6_1_75 46 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 70 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 70 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 70 123 (accept_3_5 44 70 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 70 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 70 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 70 123
  (Polychromatic418967fa.accept_11_9_4_2_1_600 42 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 70 123 (accept_3_5 41 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  70 123 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 70 123 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 70 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 70 123 (accept_3_5 38 70 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 70 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 70 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 70 123
  (Polychromatic418967fa.accept_13_10_5_6_1_1671 36 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 70 123 (accept_3_5 35 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  70 123 (Polychromatic418967fa.accept_16_2_6_11_1_1722 34 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 70 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 70 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 70 123 (accept_3_5 32 70 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 70 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 70 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 70 123
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 70 123 (accept_3_5 29 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  70 123 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 70 123 (Polychromatic418967fa.accept_13_1_5_6_1_1048 27 70 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 70 123 (accept_3_5 26 70 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 70 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 70 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 70 123
  (Polychromatic418967fa.accept_13_11_5_6_1_519 24 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 70 123 (accept_3_5 23 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  70 123 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 70 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 70 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 70 123 (accept_3_5 20 70 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 70 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 70 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 70 123
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 70 123 (accept_3_5 17 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  70 123 (Polychromatic418967fa.accept_13_3_5_6_1_3192 16 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 70 123 (Polychromatic418967fa.accept_17_15_2_4_1_2423 15 70 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 70 123 (accept_3_5 14 70 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 70 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 70 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 70 123
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 70 123 (accept_3_5 11 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  70 123 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 70 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 70 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 70 123 (accept_3_5 8 70 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 70 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 70 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 70 123
  (Polychromatic418967fa.accept_11_6_4_2_1_599 6 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 70 123 (accept_3_5 5 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 70
  123 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 70 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 70 123 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 70 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 70 123 (accept_3_5 2 70 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 70 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 70 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70 123))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 55 69 123 (Eq.refl Bool.true) (allA_succ_of_gcd 54 69 123 3 18 23 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 69 123
  (Polychromatic418967fa.accept_12_5_9_3_1_85 53 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 69 123 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 69 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 69 123 3 17 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 69 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 50
  69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 123
  (Polychromatic418967fa.accept_12_1_9_3_1_370 49 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 69 123 3 16 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 69 123 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 69 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 69 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 69 123 3 15 23 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 69 123
  (Polychromatic418967fa.accept_7_2_6_4_1_29 44 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 123 (Polychromatic418967fa.accept_12_7_9_3_1_767 43 69 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 69 123 3 14 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 69 123 (Polychromatic418967fa.accept_12_5_9_3_1_85 41
  69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 123
  (Polychromatic418967fa.accept_7_5_6_4_1_117 40 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 69 123 3 13 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 69 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 69 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 123 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 69 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 69 123 3 12 23 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 69 123
  (Polychromatic418967fa.accept_12_11_9_3_1_792 35 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 69 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 69 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 69 123 3 11 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 69 123 (Polychromatic418967fa.accept_20_12_9_3_1_5999
  32 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 123
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 69 123 3 10 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 69 123 (Polychromatic418967fa.accept_12_5_9_3_1_85 29 69 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 123 (Polychromatic418967fa.accept_13_2_4_6_1_2356 28 69 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 69 123 3 9 23 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 69 123
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 123 (Polychromatic418967fa.accept_12_1_9_3_1_370 25 69 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 69 123 3 8 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 69 123 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 69 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 123
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 69 123 3 7 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 69 123 (Polychromatic418967fa.accept_13_7_4_6_1_3221 20 69 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 123 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 69 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 69 123 3 6 23 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 69 123
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 69 123 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 69 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 69 123 3 5 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 69 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 69 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 123
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 69 123 3 4 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 69 123 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 69 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 69 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 69 123 3 3 23 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 69 123
  (Polychromatic418967fa.accept_15_8_9_3_1_1194 8 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 123 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 69 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 69 123 3 2 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 69 123 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 69 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 123
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 4 69 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 69 123 3 1 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 69 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 69 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 123 (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 69 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  123))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 68 123 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 68 123 (accept_3_4 55 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  68 123 (Polychromatic418967fa.accept_12_6_8_3_1_82 54 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 68 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 68 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 123 (accept_3_4 52 68 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 68 123 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 68 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 123
  (Polychromatic418967fa.accept_7_1_5_4_1_134 50 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 68 123 (accept_3_4 49 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  68 123 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 68 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 68 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 123 (accept_3_4 46 68 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 68 123 (Polychromatic418967fa.accept_10_5_8_3_1_229 45 68 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 123
  (Polychromatic418967fa.accept_7_2_5_4_1_115 44 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 68 123 (accept_3_4 43 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  68 123 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 68 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 68 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 123 (accept_3_4 40 68 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 68 123 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 68 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 123
  (Polychromatic418967fa.accept_9_2_5_6_1_536 38 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 68 123 (accept_3_4 37 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  68 123 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 68 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 68 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 123 (accept_3_4 34 68 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 68 123 (Polychromatic418967fa.accept_19_14_11_9_1_3330 33 68 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 123
  (Polychromatic418967fa.accept_21_11_5_18_1_5998 32 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 68 123 (accept_3_4 31 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  68 123 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 68 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 68 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 123 (accept_3_4 28 68 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 68 123 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 68 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 123
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 68 123 (accept_3_4 25 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  68 123 (Polychromatic418967fa.accept_15_9_8_3_1_557 24 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 68 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 68 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 123 (accept_3_4 22 68 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 68 123 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 68 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 123
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 68 123 (accept_3_4 19 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  68 123 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 68 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 68 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 123 (accept_3_4 16 68 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 68 123 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 68 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 123
  (Polychromatic418967fa.accept_13_1_3_6_1_158 14 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 68 123 (accept_3_4 13 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  68 123 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 68 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 68 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 123 (accept_3_4 10 68 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 68 123 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 68 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 123
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 68 123 (accept_3_4 7 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68
  123 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 68 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 68 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 123 (accept_3_4 4 68 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 68 123 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 68 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 123 (Polychromatic418967fa.accept_7_2_5_4_1_115 2
  68 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 123 (accept_3_4 1 68 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68 123))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 57 67 123 (Eq.refl Bool.true) (allA_succ_of_accept 56 67 123 (accept_3_5 56 67 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 123 (Polychromatic418967fa.accept_9_1_4_6_1_5 55 67 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 123
  (Polychromatic418967fa.accept_10_4_7_3_1_54 54 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 123 (accept_3_5 53 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 123 (Polychromatic418967fa.accept_13_12_2_6_1_2396 51 67 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 123 (accept_3_5 50 67 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 123 (Polychromatic418967fa.accept_13_10_2_6_1_1044 49 67
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 123
  (Polychromatic418967fa.accept_9_3_4_6_1_252 48 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 123 (accept_3_5 47 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 123 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 67 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 123 (accept_3_5 44 67 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 123 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 67 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 123
  (Polychromatic418967fa.accept_15_12_7_3_1_1940 42 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 123 (accept_3_5 41 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 123 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 67 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 123 (accept_3_5 38 67 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 123 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 67 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 123
  (Polychromatic418967fa.accept_10_6_7_3_1_547 36 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 123 (accept_3_5 35 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 123 (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 67 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 123 (accept_3_5 32 67 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 123 (Polychromatic418967fa.accept_16_15_3_11_1_5997 31 67 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 123
  (Polychromatic418967fa.accept_9_3_4_6_1_252 30 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 123 (accept_3_5 29 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 123 (Polychromatic418967fa.accept_13_1_2_6_1_515 27 67 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 123 (accept_3_5 26 67 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 123 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 67 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 123
  (Polychromatic418967fa.accept_10_4_7_3_1_54 24 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 123 (accept_3_5 23 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 123 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 67 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 123 (accept_3_5 20 67 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 123 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 67 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 123
  (Polychromatic418967fa.accept_19_18_10_9_1_5996 18 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 123 (accept_3_5 17 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 123 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 67 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 123 (accept_3_5 14 67 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 123 (Polychromatic418967fa.accept_19_13_10_9_1_5995 13 67 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 123
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 123 (accept_3_5 11 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 123 (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 67 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 123 (accept_3_5 8 67 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 123 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 67 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 123
  (Polychromatic418967fa.accept_10_6_7_3_1_547 6 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 123 (accept_3_5 5 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  123 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 67 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 123 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 67 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 123 (accept_3_5 2 67 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 123 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 67 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67 123)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 58 66 123 (Eq.refl Bool.true) (allA_succ_of_gcd 57 66 123 3 19 22 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 66 123
  (Polychromatic418967fa.accept_9_2_3_6_1_88 56 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 66 123 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 66 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 66 123 3 18 22 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 66 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 66
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 66 123
  (Polychromatic418967fa.accept_9_7_3_6_1_270 52 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 66 123 3 17 22 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 66 123 (Polychromatic418967fa.accept_7_1_3_4_1_128 50 66 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 66 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 123 3 16 22 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 123
  (Polychromatic418967fa.accept_9_2_3_6_1_88 47 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 66 123 (Polychromatic418967fa.accept_9_1_3_6_1_70 46 66 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 66 123 3 15 22 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 66 123 (Polychromatic418967fa.accept_9_8_3_6_1_533 44
  66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 123
  (Polychromatic418967fa.accept_7_1_3_4_1_128 43 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 66 123 3 14 22 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 66 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 66 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 123 (Polychromatic418967fa.accept_9_4_3_6_1_532 40 66 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 66 123 3 13 22 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 66 123
  (Polychromatic418967fa.accept_9_2_3_6_1_88 38 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 66 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 66 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66 123 3 12 22 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 66 123 (Polychromatic418967fa.accept_9_8_3_6_1_533 35
  66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 66 123
  (Polychromatic418967fa.accept_7_6_3_4_1_294 34 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 66 123 3 11 22 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 66 123 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 66 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 123 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 66 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 123 3 10 22 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 123
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 123 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 66 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 66 123 3 9 22 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 66 123 (Polychromatic418967fa.accept_9_8_3_6_1_533 26 66 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 123
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 66 123 3 8 22 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 66 123 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 66 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 66 123 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 66 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 66 123 3 7 22 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 66 123
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 66 123 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 66 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 123 3 6 22 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 66 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 66 123
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 66 123 3 5 22 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 66 123 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 66 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 66 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 123 3 4 22 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 123
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 123 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 66 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 66 123 3 3 22 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 66 123 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 66 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 123
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 66 123 3 2 22 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 66 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 66 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66 123 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 66 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 66 123 3 1 22 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 66 123
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 66 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 66 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 66 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 66 123)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  59 65 123 (Eq.refl Bool.true) (allA_succ_of_accept 58 65 123 (accept_3_4 58 65 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 65 123 (Polychromatic418967fa.accept_9_3_2_6_1_264 57 65 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 65 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 56
  65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 123 (accept_3_4 55 65
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 65 123 (Polychromatic418967fa.accept_4_2_1_3_1_27
  54 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 123
  (Polychromatic418967fa.accept_9_8_2_6_1_875 53 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 65 123 (accept_3_4 52 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  65 123 (Polychromatic418967fa.accept_15_6_5_3_1_1988 51 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 65 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 65 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 123 (accept_3_4 49 65 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 123 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 65 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 123
  (Polychromatic418967fa.accept_7_5_2_4_1_126 47 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 123 (accept_3_4 46 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 123 (Polychromatic418967fa.accept_11_1_10_2_1_58 45 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 65 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 123 (accept_3_4 43 65 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 65 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 123
  (Polychromatic418967fa.accept_7_6_2_4_1_291 41 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 123 (accept_3_4 40 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 123 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 65 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 123 (accept_3_4 37 65 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 123 (Polychromatic418967fa.accept_15_6_5_3_1_1988 36 65 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 123
  (Polychromatic418967fa.accept_9_8_2_6_1_875 35 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 123 (accept_3_4 34 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 123 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 65 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 123 (accept_3_4 31 65 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 65 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 123
  (Polychromatic418967fa.accept_22_7_21_13_1_5994 29 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 123 (accept_3_4 28 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 123 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 65 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 123 (accept_3_4 25 65 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 123 (Polychromatic418967fa.accept_15_9_5_3_1_554 24 65 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 123
  (Polychromatic418967fa.accept_9_5_2_6_1_265 23 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 123 (accept_3_4 22 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 123 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 65 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 123 (accept_3_4 19 65 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 65 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 123
  (Polychromatic418967fa.accept_9_8_2_6_1_875 17 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 123 (accept_3_4 16 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 123 (Polychromatic418967fa.accept_16_15_1_11_1_3747 15 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 65 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 123 (accept_3_4 13 65 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 123 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 65 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 123
  (Polychromatic418967fa.accept_19_11_8_9_1_5993 11 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 123 (accept_3_4 10 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 123 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 65 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 123 (accept_3_4 7 65 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 65 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 123
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 123 (accept_3_4 4 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  123 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 65 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 65 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 123 (accept_3_4 1 65 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 123))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 64 123 (Eq.refl
  Bool.true) (allA_succ_of_accept 59 64 123 (accept_3_5 59 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 64 123 (Polychromatic418967fa.accept_9_4_1_6_1_284 58 64 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 64 123 (Polychromatic418967fa.accept_9_3_1_6_1_86 57 64 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 64 123 (accept_3_5 56 64 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 64 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 55
  64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 64 123
  (Polychromatic418967fa.accept_7_5_1_4_1_122 54 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 64 123 (accept_3_5 53 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  64 123 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 64 123 (Polychromatic418967fa.accept_11_7_9_2_1_260 51 64 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 64 123 (accept_3_5 50 64 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 64 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 64 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 64 123
  (Polychromatic418967fa.accept_9_3_1_6_1_86 48 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 64 123 (accept_3_5 47 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  64 123 (Polychromatic418967fa.accept_13_7_12_6_1_1039 46 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 64 123 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 64 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 64 123 (accept_3_5 44 64 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 64 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 64 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 64 123
  (Polychromatic418967fa.accept_12_6_4_3_1_361 42 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 64 123 (accept_3_5 41 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  64 123 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 64 123 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 64 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 64 123 (accept_3_5 38 64 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 64 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 64 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 64 123
  (Polychromatic418967fa.accept_13_10_12_6_1_991 36 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 64 123 (accept_3_5 35 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  64 123 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 64 123 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 64 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 64 123 (accept_3_5 32 64 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 64 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 64 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 64 123
  (Polychromatic418967fa.accept_9_3_1_6_1_86 30 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 64 123 (accept_3_5 29 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  64 123 (Polychromatic418967fa.accept_13_2_12_6_1_2394 28 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 64 123 (Polychromatic418967fa.accept_10_7_4_3_1_560 27 64 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 64 123 (accept_3_5 26 64 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 64 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 64 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 64 123
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 64 123 (accept_3_5 23 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  64 123 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 64 123 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 64 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 64 123 (accept_3_5 20 64 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 64 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 64 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 64 123
  (Polychromatic418967fa.accept_11_7_9_2_1_260 18 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 64 123 (accept_3_5 17 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  64 123 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 64 123 (Polychromatic418967fa.accept_11_4_9_2_1_259 15 64 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 64 123 (accept_3_5 14 64 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 64 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 64 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 64 123
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 64 123 (accept_3_5 11 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  64 123 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 64 123 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 64 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 64 123 (accept_3_5 8 64 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 64 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 64 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 64 123
  (Polychromatic418967fa.accept_12_6_4_3_1_361 6 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 64 123 (accept_3_5 5 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 64
  123 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 64 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 64 123 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 64 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 64 123 (accept_3_5 2 64 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 64 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 64 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64 123))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 61 63 123 (Eq.refl Bool.true) (allA_succ_of_gcd 60 63 123 3 20 21 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 63 123
  (Polychromatic418967fa.accept_14_3_7_11_1_765 59 63 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 63 123 (Polychromatic418967fa.accept_16_10_15_11_1_3785 58 63 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 63 123 3 19 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 63 123 (Polychromatic418967fa.accept_13_4_11_6_1_1033
  56 63 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 63 123
  (Polychromatic418967fa.accept_16_7_15_11_1_951 55 63 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 63 123 3 18 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 63 123 (Polychromatic418967fa.accept_17_2_12_4_1_5987 53 63 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 123 (Polychromatic418967fa.accept_8_4_7_3_1_144 52 63 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 63 123 3 17 21 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 63 123
  (Polychromatic418967fa.accept_22_6_19_13_1_5992 50 63 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 123 (Polychromatic418967fa.accept_11_5_8_2_1_588 49 63 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 63 123 3 16 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 63 123 (Polychromatic418967fa.accept_13_8_11_6_1_1035
  47 63 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 123
  (Polychromatic418967fa.accept_14_4_7_11_1_790 46 63 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 63 123 3 15 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 63 123 (Polychromatic418967fa.accept_8_4_7_3_1_144 44 63 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 123 (Polychromatic418967fa.accept_13_4_11_6_1_1033 43 63
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 63 123 3 14 21 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 63 123
  (Polychromatic418967fa.accept_17_7_12_4_1_2524 41 63 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 63 123 (Polychromatic418967fa.accept_18_4_9_15_1_3383 40 63 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 63 123 3 13 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 63 123 (Polychromatic418967fa.accept_11_5_8_2_1_588 38
  63 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 123
  (Polychromatic418967fa.accept_19_18_6_9_1_5991 37 63 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 63 123 3 12 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 63 123 (Polychromatic418967fa.accept_16_3_15_11_1_2676 35 63 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 123 (Polychromatic418967fa.accept_13_8_11_6_1_1035 34 63
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 63 123 3 11 21 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 63 123
  (Polychromatic418967fa.accept_14_4_7_11_1_790 32 63 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 123 (Polychromatic418967fa.accept_13_5_11_6_1_505 31 63 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 63 123 3 10 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 63 123 (Polychromatic418967fa.accept_18_11_9_15_1_5988
  29 63 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 123
  (Polychromatic418967fa.accept_8_4_7_3_1_144 28 63 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 63 123 3 9 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 63 123 (Polychromatic418967fa.accept_16_10_15_11_1_3785 26 63 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 123 (Polychromatic418967fa.accept_17_8_12_4_1_2525 25 63
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 63 123 3 8 21 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 63 123
  (Polychromatic418967fa.accept_16_7_15_11_1_951 23 63 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 63 123 (Polychromatic418967fa.accept_18_4_9_15_1_3383 22 63 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63 123 3 7 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 63 123 (Polychromatic418967fa.accept_8_4_7_3_1_144 20 63 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 123
  (Polychromatic418967fa.accept_16_3_15_11_1_2676 19 63 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 63 123 3 6 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 63 123 (Polychromatic418967fa.accept_13_4_11_6_1_1033 17 63 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 123 (Polychromatic418967fa.accept_11_5_8_2_1_588 16 63 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 63 123 3 5 21 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 63 123
  (Polychromatic418967fa.accept_19_14_6_9_1_5990 14 63 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 123 (Polychromatic418967fa.accept_19_13_6_9_1_5989 13 63 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 63 123 3 4 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 63 123 (Polychromatic418967fa.accept_18_11_9_15_1_5988 11 63
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 123
  (Polychromatic418967fa.accept_14_10_7_11_1_3015 10 63 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 63 123 3 3 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 63 123 (Polychromatic418967fa.accept_13_8_11_6_1_1035 8 63 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 123 (Polychromatic418967fa.accept_16_7_15_11_1_951 7 63 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 63 123 3 2 21 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 63 123
  (Polychromatic418967fa.accept_11_5_8_2_1_588 5 63 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 63 123 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 63 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 63 123 3 1 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 63 123 (Polychromatic418967fa.accept_17_2_12_4_1_5987 2 63 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 123
  (Polychromatic418967fa.accept_16_1_15_11_1_356 1 63 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 63 123))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 123 (allA_succ_of_accept
  61 62 123 (accept_3_4 61 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 123
  (Polychromatic418967fa.accept_22_16_18_13_1_5986 60 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 62 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 62 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 123 (accept_3_4 58 62 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 62 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 62 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 123
  (Polychromatic418967fa.accept_9_2_8_6_1_79 56 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 62 123 (accept_3_4 55 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  62 123 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 62 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 62 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 123 (accept_3_4 52 62 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 62 123 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 62 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 123
  (Polychromatic418967fa.accept_9_5_8_6_1_281 50 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 62 123 (accept_3_4 49 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  62 123 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 62 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 62 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 123 (accept_3_4 46 62 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 62 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 62 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 123
  (Polychromatic418967fa.accept_7_2_6_4_1_29 44 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 62 123 (accept_3_4 43 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  62 123 (Polychromatic418967fa.accept_11_9_7_2_1_1068 42 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 62 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 62 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 123 (accept_3_4 40 62 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 62 123 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 62 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 123
  (Polychromatic418967fa.accept_7_3_6_4_1_30 38 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 62 123 (accept_3_4 37 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  62 123 (Polychromatic418967fa.accept_21_15_20_18_1_5985 36 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 62 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 62 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 62 123 (accept_3_4 34 62 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 62 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 62 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 62 123
  (Polychromatic418967fa.accept_9_5_8_6_1_281 32 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 62 123 (accept_3_4 31 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  62 123 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 62 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 62 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 62 123 (accept_3_4 28 62 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 62 123 (Polychromatic418967fa.accept_15_12_2_3_1_1146 27 62 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 62 123
  (Polychromatic418967fa.accept_7_5_6_4_1_117 26 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 62 123 (accept_3_4 25 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  62 123 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 62 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 62 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 62 123 (accept_3_4 22 62 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 62 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 62 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 62 123
  (Polychromatic418967fa.accept_9_2_8_6_1_79 20 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 62 123 (accept_3_4 19 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  62 123 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 62 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 62 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 62 123 (accept_3_4 16 62 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 62 123 (Polychromatic418967fa.accept_10_5_2_3_1_239 15 62 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 62 123
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 62 123 (accept_3_4 13 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  62 123 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 62 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 62 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 62 123 (accept_3_4 10 62 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 62 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 62 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 62 123
  (Polychromatic418967fa.accept_29_8_4_7_1_5984 8 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 62 123 (accept_3_4 7 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 62
  123 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 62 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 62 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 62 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 123 (accept_3_4 4 62 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 62 123 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 62 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 123 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 62
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 123 (accept_3_4 1 62 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  123)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 123 (allA_succ_of_accept 60 61 123
  (Polychromatic418967fa.accept_24_12_13_3_1_351 60 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 123 (accept_3_5 59 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 123 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 61 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 123 (accept_3_5 56 61 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 123 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 61 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 123
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 123 (accept_3_5 53 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 123 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 61 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 123 (accept_3_5 50 61 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 123 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 61 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 123
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 123 (accept_3_5 47 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 123 (Polychromatic418967fa.accept_12_9_1_3_1_350 45 61 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 123 (accept_3_5 44 61 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 123 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 61 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 123
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 123 (accept_3_5 41 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 123 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 61 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 123 (accept_3_5 38 61 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 123 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 61 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 123
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 123 (accept_3_5 35 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 123 (Polychromatic418967fa.accept_12_9_1_3_1_350 33 61 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 123 (accept_3_5 32 61 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 123 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 61 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 123
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 123 (accept_3_5 29 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 123 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 61 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 123 (accept_3_5 26 61 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 123 (Polychromatic418967fa.accept_20_5_1_3_1_5983 25 61 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 123
  (Polychromatic418967fa.accept_16_8_13_11_1_4772 24 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 123 (accept_3_5 23 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 123 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 61 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 123 (accept_3_5 20 61 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 123 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 61 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 123
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 123 (accept_3_5 17 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 123 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 61 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 123 (accept_3_5 14 61 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 123 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 61 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 123
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 123 (accept_3_5 11 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 123 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 61 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 123 (accept_3_5 8 61 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 123 (Polychromatic418967fa.accept_13_7_9_6_1_148 7 61 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 123
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 123 (accept_3_5 5 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  123 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 61 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 123 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 61 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 123 (accept_3_5 2 61 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 123 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 61 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 123)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 123 (allA_succ_of_accept 59 60 123 (Polychromatic418967fa.accept_18_5_6_15_1_3413 59 60 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 60 123
  (Polychromatic418967fa.accept_16_10_12_11_1_346 58 60 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 60 123 3 19 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 60 123 (Polychromatic418967fa.accept_16_8_12_11_1_3697 56 60 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 123 (Polychromatic418967fa.accept_8_7_4_3_1_156 55 60 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 123 3 18 20 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 123
  (Polychromatic418967fa.accept_13_1_8_6_1_1016 53 60 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 60 123 (Polychromatic418967fa.accept_11_8_5_2_1_1629 52 60 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 60 123 3 17 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 60 123 (Polychromatic418967fa.accept_13_11_8_6_1_1023
  50 60 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 123
  (Polychromatic418967fa.accept_14_7_4_11_1_3038 49 60 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 60 123 3 16 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 60 123 (Polychromatic418967fa.accept_8_7_4_3_1_156 47 60 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 60 123 (Polychromatic418967fa.accept_17_12_9_4_1_5982 46 60
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 60 123 3 15 20 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 60 123
  (Polychromatic418967fa.accept_19_6_3_9_1_3332 44 60 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 60 123 (Polychromatic418967fa.accept_14_1_4_11_1_3036 43 60 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 123 3 14 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 123 (Polychromatic418967fa.accept_11_8_5_2_1_1629
  41 60 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 60 123
  (Polychromatic418967fa.accept_13_1_8_6_1_1016 40 60 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 60 123 3 13 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 60 123 (Polychromatic418967fa.accept_25_13_10_23_1_5981 38 60 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 123 (Polychromatic418967fa.accept_13_11_8_6_1_1023 37 60
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 123 3 12 20 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 123
  (Polychromatic418967fa.accept_14_7_4_11_1_3038 35 60 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 60 123 (Polychromatic418967fa.accept_18_16_6_15_1_3376 34 60 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 60 123 3 11 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 60 123 (Polychromatic418967fa.accept_19_13_3_9_1_5980
  32 60 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 123
  (Polychromatic418967fa.accept_8_7_4_3_1_156 31 60 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 60 123 3 10 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 60 123 (Polychromatic418967fa.accept_14_1_4_11_1_3036 29 60 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 60 123 (Polychromatic418967fa.accept_13_2_8_6_1_2390 28 60 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 60 123 3 9 20 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 60 123
  (Polychromatic418967fa.accept_16_10_12_11_1_346 26 60 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 60 123 (Polychromatic418967fa.accept_19_6_3_9_1_3332 25 60 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 123 3 8 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 123 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 60 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 60 123
  (Polychromatic418967fa.accept_14_8_4_11_1_3035 22 60 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 60 123 3 7 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 60 123 (Polychromatic418967fa.accept_16_4_12_11_1_2650 20 60 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 123 (Polychromatic418967fa.accept_11_8_5_2_1_1629 19 60 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 123 3 6 20 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 123
  (Polychromatic418967fa.accept_16_1_12_11_1_2648 17 60 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 60 123 (Polychromatic418967fa.accept_18_16_6_15_1_3376 16 60 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 60 123 3 5 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 60 123 (Polychromatic418967fa.accept_13_1_8_6_1_1016 14 60 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 123
  (Polychromatic418967fa.accept_17_13_9_4_1_5979 13 60 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 60 123 3 4 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 60 123 (Polychromatic418967fa.accept_13_11_8_6_1_1023 11 60 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 60 123 (Polychromatic418967fa.accept_16_10_12_11_1_346 10 60
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 60 123 3 3 20 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 60 123
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 8 60 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 60 123 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 60 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 123 3 2 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 123 (Polychromatic418967fa.accept_18_5_6_15_1_3413 5 60 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 60 123
  (Polychromatic418967fa.accept_16_4_12_11_1_2650 4 60 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 60 123 3 1 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 60 123 (Polychromatic418967fa.accept_13_2_8_6_1_2390 2 60 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 123 (Polychromatic418967fa.accept_13_1_8_6_1_1016 1 60 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  123)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 123 (allA_succ_of_accept 58 59 123
  (accept_3_4 58 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 123
  (Polychromatic418967fa.accept_7_1_3_4_1_128 57 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 59 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 123 (accept_3_4 55 59 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 123 (Polychromatic418967fa.accept_10_4_9_3_1_1907 54 59 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 123 (Polychromatic418967fa.accept_9_8_5_6_1_538 53
  59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 59 123 (accept_3_4 52 59
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 59 123
  (Polychromatic418967fa.accept_13_12_7_6_1_1015 51 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 59 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 59 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 123 (accept_3_4 49 59 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 59 123 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 59 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 123 (Polychromatic418967fa.accept_9_2_5_6_1_536 47
  59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 59 123 (accept_3_4 46 59
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 59 123
  (Polychromatic418967fa.accept_12_9_11_3_1_772 45 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 59 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 59 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 123 (accept_3_4 43 59 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 59 123 (Polychromatic418967fa.accept_11_9_4_2_1_600 42 59 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 123 (Polychromatic418967fa.accept_7_6_3_4_1_294 41
  59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 59 123 (accept_3_4 40 59
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 59 123
  (Polychromatic418967fa.accept_9_3_5_6_1_253 39 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 59 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 59 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 123 (accept_3_4 37 59 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 59 123 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 59 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 123 (Polychromatic418967fa.accept_9_8_5_6_1_538 35
  59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 59 123 (accept_3_4 34 59
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 59 123
  (Polychromatic418967fa.accept_12_9_11_3_1_772 33 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 59 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 59 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 123 (accept_3_4 31 59 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 59 123 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 59 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 123 (Polychromatic418967fa.accept_7_1_3_4_1_128 29
  59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 59 123 (accept_3_4 28 59
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 59 123
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 59 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 59 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 123 (accept_3_4 25 59 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 59 123 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 59 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 123 (Polychromatic418967fa.accept_19_4_2_9_1_4584
  23 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 59 123 (accept_3_4 22
  59 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 59 123
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 59 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 59 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 123 (accept_3_4 19 59 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 59 123 (Polychromatic418967fa.accept_17_1_8_4_1_1519 18 59 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 123 (Polychromatic418967fa.accept_9_8_5_6_1_538 17
  59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 59 123 (accept_3_4 16 59
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 59 123
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 59 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 59 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 123 (accept_3_4 13 59 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 59 123 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 59 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 123 (Polychromatic418967fa.accept_9_2_5_6_1_536 11
  59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 59 123 (accept_3_4 10 59
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 59 123
  (Polychromatic418967fa.accept_11_9_4_2_1_600 9 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 59 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 59 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 123 (accept_3_4 7 59 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 59 123 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 59 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 123 (Polychromatic418967fa.accept_23_5_13_8_1_5978
  5 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 123 (accept_3_4 4 59
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59 123 (Polychromatic418967fa.accept_9_3_5_6_1_253
  3 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 123
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 59 123 (accept_3_4 1 59 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59
  123))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 123 (allA_succ_of_accept 57 58 123
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 58 123 (accept_3_5 56 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  58 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 58 123 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 58 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 58 123 (accept_3_5 53 58 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 58 123 (Polychromatic418967fa.accept_9_7_4_6_1_273 52 58 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 58 123
  (Polychromatic418967fa.accept_10_1_8_3_1_947 51 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 58 123 (accept_3_5 50 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  58 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 58 123 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 58 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 58 123 (accept_3_5 47 58 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 58 123 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 58 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 58 123
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 58 123 (accept_3_5 44 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  58 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 58 123 (Polychromatic418967fa.accept_12_6_10_3_1_1313 42 58 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 58 123 (accept_3_5 41 58 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 58 123 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 58 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 58 123
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 58 123 (accept_3_5 38 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  58 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 58 123 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 58 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 58 123 (accept_3_5 35 58 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 58 123 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 58 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 58 123
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 58 123 (accept_3_5 32 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  58 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 58 123 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 58 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 58 123 (accept_3_5 29 58 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 58 123 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 58 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 58 123
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 58 123 (accept_3_5 26 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  58 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 58 123 (Polychromatic418967fa.accept_15_9_13_3_1_535 24 58 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 58 123 (accept_3_5 23 58 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 58 123 (Polychromatic418967fa.accept_20_2_18_3_1_4519 22 58 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 58 123
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 58 123 (accept_3_5 20 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  58 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 58 123 (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 58 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 58 123 (accept_3_5 17 58 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 58 123 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 58 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 58 123
  (Polychromatic418967fa.accept_10_5_8_3_1_229 15 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 58 123 (accept_3_5 14 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  58 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 58 123 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 58 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 58 123 (accept_3_5 11 58 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 58 123 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 58 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 58 123
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 58 123 (accept_3_5 8 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 58
  123 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 58 123 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 58 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 58 123 (accept_3_5 5 58 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 58 123 (Polychromatic418967fa.accept_22_4_14_13_1_5977 4 58 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 58 123 (Polychromatic418967fa.accept_9_3_4_6_1_252 3
  58 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 123 (accept_3_5 2 58 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 58 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 58
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  123)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 123 (allA_succ_of_accept 56 57 123
  (Polychromatic418967fa.accept_9_2_3_6_1_88 56 57 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 123 (Polychromatic418967fa.accept_9_1_3_6_1_70 55 57 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 57 123 3 18 19 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 57 123 (Polychromatic418967fa.accept_9_8_3_6_1_533 53
  57 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 123
  (Polychromatic418967fa.accept_7_3_1_4_1_121 52 57 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 57 123 3 17 19 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 57 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 57 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 123 (Polychromatic418967fa.accept_9_4_3_6_1_532 49 57 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 57 123 3 16 19 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 57 123
  (Polychromatic418967fa.accept_7_5_1_4_1_122 47 57 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 57 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 57 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 57 123 3 15 19 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 57 123 (Polychromatic418967fa.accept_9_8_3_6_1_533 44
  57 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 123
  (Polychromatic418967fa.accept_9_7_3_6_1_270 43 57 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 57 123 3 14 19 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 57 123 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 57 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 123 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 57 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 57 123 3 13 19 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 57 123
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 57 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 123 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 57 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 57 123 3 12 19 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 57 123 (Polychromatic418967fa.accept_9_8_3_6_1_533 35
  57 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 123
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 57 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 57 123 3 11 19 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 57 123 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 57 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 123 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 57 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 57 123 3 10 19 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 57 123
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 57 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 57 123 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 57 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 57 123 3 9 19 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 57 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 57 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 123
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 57 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 57 123 3 8 19 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 57 123 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 57 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 57 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 57 123 3 7 19 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 57 123
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 57 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 123 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 57 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 57 123 3 6 19 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 57 123 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 57 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 123
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 57 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 57 123 3 5 19 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 57 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 57 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 123 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 57 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 57 123 3 4 19 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 57 123
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 57 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 57 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 57 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 57 123 3 3 19 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 57 123 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 57 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 123
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 57 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 57 123 3 2 19 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 57 123 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 57 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 123 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 57 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 57 123 3 1 19 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 57 123
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 57 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 57 123 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 57 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 57 123))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  56 123 (allA_succ_of_accept 55 56 123 (accept_3_4 55 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 56 123 (Polychromatic418967fa.accept_11_10_1_2_1_1624 54 56 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 56 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 56 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 123 (accept_3_4 52 56 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 56 123 (Polychromatic418967fa.accept_15_6_11_3_1_1172
  51 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 123
  (Polychromatic418967fa.accept_9_5_2_6_1_265 50 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 56 123 (accept_3_4 49 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  56 123 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 56 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 56 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 123 (accept_3_4 46 56 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 56 123 (Polychromatic418967fa.accept_16_13_8_11_1_4785 45 56 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 123
  (Polychromatic418967fa.accept_9_8_2_6_1_875 44 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 123 (accept_3_4 43 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  56 123 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 56 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 56 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 123 (accept_3_4 40 56 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 123 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 56 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 123
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 38 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 56 123 (accept_3_4 37 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  56 123 (Polychromatic418967fa.accept_11_3_1_2_1_1063 36 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 56 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 56 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 123 (accept_3_4 34 56 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 123 (Polychromatic418967fa.accept_13_7_4_6_1_3221 33 56 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 123
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 56 123 (accept_3_4 31 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  56 123 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 56 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 56 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 123 (accept_3_4 28 56 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 56 123 (Polychromatic418967fa.accept_10_7_6_3_1_927 27 56 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 123
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 56 123 (accept_3_4 25 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  56 123 (Polychromatic418967fa.accept_13_11_4_6_1_1006 24 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 56 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 56 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 123 (accept_3_4 22 56 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 56 123 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 56 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 123
  (Polychromatic418967fa.accept_13_7_4_6_1_3221 20 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 56 123 (accept_3_4 19 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  56 123 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 56 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 56 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 123 (accept_3_4 16 56 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 123 (Polychromatic418967fa.accept_13_2_4_6_1_2356 15 56 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 123
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 56 123 (accept_3_4 13 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  56 123 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 56 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 56 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 123 (accept_3_4 10 56 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 123 (Polychromatic418967fa.accept_10_9_6_3_1_545 9 56 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 123
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 56 123 (accept_3_4 7 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56
  123 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 56 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 56 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 123 (accept_3_4 4 56 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 56 123 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 56 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 123 (Polychromatic418967fa.accept_13_2_4_6_1_2356 2
  56 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 123 (accept_3_4 1 56 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 123))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 123 (allA_succ_of_accept 54 55 123 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 55 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 123 (accept_3_5 53 55 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 55 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 55 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 123
  (Polychromatic418967fa.accept_7_2_6_4_1_29 51 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 55 123 (accept_3_5 50 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  55 123 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 55 123 (Polychromatic418967fa.accept_9_3_1_6_1_86 48 55 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 123 (accept_3_5 47 55 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 55 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 55 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 55 123
  (Polychromatic418967fa.accept_7_3_6_4_1_30 45 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 55 123 (accept_3_5 44 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  55 123 (Polychromatic418967fa.accept_9_7_1_6_1_261 43 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 55 123 (Polychromatic418967fa.accept_10_2_5_3_1_1408 42 55 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 55 123 (accept_3_5 41 55 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 55 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 55 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 55 123
  (Polychromatic418967fa.accept_9_3_1_6_1_86 39 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 55 123 (accept_3_5 38 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  55 123 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 55 123 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 55 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 55 123 (accept_3_5 35 55 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 55 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 55 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 55 123
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 55 123 (accept_3_5 32 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  55 123 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 55 123 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 55 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 55 123 (accept_3_5 29 55 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 55 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 123
  (Polychromatic418967fa.accept_10_7_5_3_1_542 27 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 123 (accept_3_5 26 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  55 123 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 55 123 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 55 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 123 (accept_3_5 23 55 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 55 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 55 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 123
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 55 123 (accept_3_5 20 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  55 123 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 55 123 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 55 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 123 (accept_3_5 17 55 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 55 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 55 123
  (Polychromatic418967fa.accept_16_15_7_11_1_3760 15 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 55 123 (accept_3_5 14 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  55 123 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 55 123 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 55 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 123 (accept_3_5 11 55 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 55 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 55 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 123
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 55 123 (accept_3_5 8 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55
  123 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 55 123 (Polychromatic418967fa.accept_15_6_10_3_1_2844 6 55 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 55 123 (accept_3_5 5 55 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 55 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 55 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 123 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 55
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 123 (accept_3_5 2 55 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 123 (Polychromatic418967fa.accept_13_1_3_6_1_158 1
  55 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55
  123))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 123 (allA_succ_of_accept 53 54 123
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 54 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 54 123 (Polychromatic418967fa.accept_12_4_6_3_1_332 52 54 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 54 123 3 17 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 54 123 (Polychromatic418967fa.accept_7_1_5_4_1_134 50
  54 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 123
  (Polychromatic418967fa.accept_4_1_2_3_1_9 49 54 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 54 123 3 16 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 54 123 (Polychromatic418967fa.accept_10_7_4_3_1_560 47 54 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 123 (Polychromatic418967fa.accept_12_10_6_3_1_786 46 54 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 54 123 3 15 18 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 54 123
  (Polychromatic418967fa.accept_7_2_5_4_1_115 44 54 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 54 123 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 54 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 123 3 14 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 54
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 123
  (Polychromatic418967fa.accept_12_4_6_3_1_332 40 54 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 54 123 3 13 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 54 123 (Polychromatic418967fa.accept_12_2_6_3_1_331 38 54 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 54 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 123 3 12 18 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 123
  (Polychromatic418967fa.accept_13_9_2_6_1_514 35 54 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 54 123 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 54 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 54 123 3 11 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 54 123 (Polychromatic418967fa.accept_12_8_6_3_1_366 32
  54 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 123
  (Polychromatic418967fa.accept_19_12_16_9_1_5976 31 54 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 54 123 3 10 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 54 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 54 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 123 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 54 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 54 123 3 9 18 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 54 123
  (Polychromatic418967fa.accept_12_2_6_3_1_331 26 54 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 54 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 54 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 123 3 8 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 123 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 54 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 123
  (Polychromatic418967fa.accept_7_1_5_4_1_134 22 54 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 54 123 3 7 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 54 123 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 54 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 123 (Polychromatic418967fa.accept_10_9_4_3_1_539 19 54 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 123 3 6 18 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 123
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 54 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 54 123 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 54 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 54 123 3 5 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 54 123 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 54 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 123
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 54 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 54 123 3 4 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 54 123 (Polychromatic418967fa.accept_20_11_14_3_1_5975 11 54 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 123 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 54 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 54 123 3 3 18 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 54 123
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 54 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 54 123 (Polychromatic418967fa.accept_10_7_4_3_1_560 7 54 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 123 3 2 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 54 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 123
  (Polychromatic418967fa.accept_12_4_6_3_1_332 4 54 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 54 123 3 1 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 54 123 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 54 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 54 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  123)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 123 (allA_succ_of_accept 52 53 123 (accept_3_4
  52 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 123
  (Polychromatic418967fa.accept_11_7_9_2_1_260 51 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 53 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 123 (accept_3_4 49 53 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 123 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 53 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 123 (Polychromatic418967fa.accept_9_2_8_6_1_79 47
  53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 123 (accept_3_4 46 53
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 123
  (Polychromatic418967fa.accept_12_9_5_3_1_782 45 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 53 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 53 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 123 (accept_3_4 43 53 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 53 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 53 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 123 (Polychromatic418967fa.accept_9_5_8_6_1_281 41
  53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 123 (accept_3_4 40 53
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 123 (Polychromatic418967fa.accept_9_3_8_6_1_80
  39 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 53 123
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 53 123 (accept_3_4 37 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  53 123 (Polychromatic418967fa.accept_20_16_13_3_1_5974 36 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 53 123 (Polychromatic418967fa.accept_13_9_1_6_1_510 35 53 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 53 123 (accept_3_4 34 53 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 53 123 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 53 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 53 123
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 53 123 (accept_3_4 31 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  53 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 53 123 (Polychromatic418967fa.accept_9_2_8_6_1_79 29 53 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 123 (accept_3_4 28 53 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 53 123 (Polychromatic418967fa.accept_15_12_8_3_1_1995 27 53 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 53 123
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 53 123 (accept_3_4 25 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  53 123 (Polychromatic418967fa.accept_15_9_8_3_1_557 24 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 53 123 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 53 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 53 123 (accept_3_4 22 53 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 53 123 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 53 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 53 123
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 53 123 (accept_3_4 19 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  53 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 53 123 (Polychromatic418967fa.accept_27_17_26_15_1_5973 17 53 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 123 (accept_3_4 16 53 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 53 123 (Polychromatic418967fa.accept_11_4_9_2_1_259 15 53 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 123
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 53 123 (accept_3_4 13 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  53 123 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 53 123 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 53 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 123 (accept_3_4 10 53 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 53 123 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 53 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 123
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 53 123 (accept_3_4 7 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53
  123 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 53 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 53 123 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 53 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 53 123 (accept_3_4 4 53 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 53 123 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 53 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 53 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 53
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 123 (accept_3_4 1 53 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 53 123)))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 52 123 (allA_succ_of_accept 51 52 123 (Polychromatic418967fa.accept_10_1_2_3_1_1910 51 52 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 123 (accept_3_5 50 52 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 52 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 52 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 123
  (Polychromatic418967fa.accept_7_6_3_4_1_294 48 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 52 123 (accept_3_5 47 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  52 123 (Polychromatic418967fa.accept_9_1_7_6_1_75 46 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 52 123 (Polychromatic418967fa.accept_10_5_2_3_1_239 45 52 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 123 (accept_3_5 44 52 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 52 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 52 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 123
  (Polychromatic418967fa.accept_12_6_4_3_1_361 42 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 52 123 (accept_3_5 41 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  52 123 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 52 123 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 52 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 52 123 (accept_3_5 38 52 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 52 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 52 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 52 123
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 52 123 (accept_3_5 35 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  52 123 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 52 123 (Polychromatic418967fa.accept_20_13_12_3_1_5972 33 52 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 52 123 (accept_3_5 32 52 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 52 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 52 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 52 123
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 52 123 (accept_3_5 29 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  52 123 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 52 123 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 52 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 52 123 (accept_3_5 26 52 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 52 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 52 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 123
  (Polychromatic418967fa.accept_16_8_4_11_1_2687 24 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 52 123 (accept_3_5 23 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  52 123 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 52 123 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 52 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 52 123 (accept_3_5 20 52 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 52 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 52 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 52 123
  (Polychromatic418967fa.accept_12_6_4_3_1_361 18 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 52 123 (accept_3_5 17 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  52 123 (Polychromatic418967fa.accept_11_5_8_2_1_588 16 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 52 123 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 52 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 52 123 (accept_3_5 14 52 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 52 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 52 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 52 123
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 52 123 (accept_3_5 11 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  52 123 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 52 123 (Polychromatic418967fa.accept_16_9_4_11_1_2661 9 52 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 123 (accept_3_5 8 52 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 52 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 52 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 123
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 52 123 (accept_3_5 5 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52
  123 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 52 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 52 123 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 52 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 123 (accept_3_5 2 52 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 52 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 52 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52 123))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 51 123 (allA_succ_of_accept 50 51 123 (Polychromatic418967fa.accept_15_5_6_3_1_525 50 51 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 123
  (Polychromatic418967fa.accept_13_10_12_6_1_991 49 51 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 51 123 3 16 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 51 123 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 51 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 123 (Polychromatic418967fa.accept_13_7_12_6_1_1039 46 51
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 51 123 3 15 17 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 51 123
  (Polychromatic418967fa.accept_13_5_12_6_1_508 44 51 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 123 (Polychromatic418967fa.accept_19_5_13_9_1_5957 43 51 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 51 123 3 14 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 51 123 (Polychromatic418967fa.accept_7_6_2_4_1_291 41
  51 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 123
  (Polychromatic418967fa.accept_7_5_2_4_1_126 40 51 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 51 123 3 13 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 51 123 (Polychromatic418967fa.accept_10_8_1_3_1_1374 38 51 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 123 (Polychromatic418967fa.accept_19_18_13_9_1_5971 37 51
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 51 123 3 12 17 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 51 123
  (Polychromatic418967fa.accept_15_5_6_3_1_525 35 51 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 51 123 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 51 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 51 123 3 11 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 51 123 (Polychromatic418967fa.accept_10_2_1_3_1_233 32
  51 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 123
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 31 51 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 51 123 3 10 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 51 123 (Polychromatic418967fa.accept_19_10_13_9_1_4552 29 51 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 123 (Polychromatic418967fa.accept_10_8_1_3_1_1374 28 51 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 51 123 3 9 17 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 51 123
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 51 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 123 (Polychromatic418967fa.accept_15_10_6_3_1_1160 25 51 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 51 123 3 8 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 51 123 (Polychromatic418967fa.accept_13_10_12_6_1_991 23 51 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 123
  (Polychromatic418967fa.accept_10_2_1_3_1_233 22 51 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 51 123 3 7 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 51 123 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 51 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 123 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 51 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 51 123 3 6 17 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 51 123
  (Polychromatic418967fa.accept_19_17_13_9_1_5970 17 51 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 51 123 (Polychromatic418967fa.accept_14_2_9_11_1_3054 16 51 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 51 123 3 5 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 51 123 (Polychromatic418967fa.accept_16_14_3_11_1_5969 14 51
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 123
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 51 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 51 123 3 4 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 51 123 (Polychromatic418967fa.accept_15_11_6_3_1_1192 11 51 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 123 (Polychromatic418967fa.accept_13_10_12_6_1_991 10 51
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 51 123 3 3 17 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 51 123
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 8 51 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 123 (Polychromatic418967fa.accept_13_7_12_6_1_1039 7 51 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 51 123 3 2 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 51 123 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 51 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 123
  (Polychromatic418967fa.accept_19_4_13_9_1_5968 4 51 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 51 123 3 1 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 51 123 (Polychromatic418967fa.accept_10_2_1_3_1_233 2 51 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 123 (Polychromatic418967fa.accept_15_1_6_3_1_2827 1 51 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  123))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 123 (allA_succ_of_accept 49 50 123 (accept_3_4 49
  50 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 50 123
  (Polychromatic418967fa.accept_9_3_5_6_1_253 48 50 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 50 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 50 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 123 (accept_3_4 46 50 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 50 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 50 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 123 (Polychromatic418967fa.accept_9_8_5_6_1_538 44
  50 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 50 123 (accept_3_4 43 50
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 50 123
  (Polychromatic418967fa.accept_12_6_2_3_1_354 42 50 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 50 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 50 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 50 123 (accept_3_4 40 50 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 50 123 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 50 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 123 (Polychromatic418967fa.accept_7_3_1_4_1_121 38
  50 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 50 123 (accept_3_4 37 50
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 50 123
  (Polychromatic418967fa.accept_15_6_5_3_1_1988 36 50 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 50 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 50 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 123 (accept_3_4 34 50 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 50 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 50 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 123 (Polychromatic418967fa.accept_14_4_8_11_1_794
  32 50 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 50 123 (accept_3_4 31
  50 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 50 123
  (Polychromatic418967fa.accept_9_3_5_6_1_253 30 50 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 50 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 50 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 123 (accept_3_4 28 50 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 50 123 (Polychromatic418967fa.accept_20_7_10_3_1_949 27 50 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 123 (Polychromatic418967fa.accept_7_5_1_4_1_122 26
  50 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 50 123 (accept_3_4 25 50
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 50 123
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 50 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 50 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 50 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 123 (accept_3_4 22 50 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 50 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 50 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 123 (Polychromatic418967fa.accept_9_2_5_6_1_536 20
  50 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 50 123 (accept_3_4 19 50
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 50 123
  (Polychromatic418967fa.accept_12_6_2_3_1_354 18 50 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 50 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 50 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 123 (accept_3_4 16 50 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 50 123 (Polychromatic418967fa.accept_11_4_6_2_1_51 15 50 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 123
  (Polychromatic418967fa.accept_19_14_12_9_1_4587 14 50 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 50 123 (accept_3_4 13 50 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  50 123 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 50 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 50 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 50 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 123 (accept_3_4 10 50 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 50 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 50 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 123
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 50 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 50 123 (accept_3_4 7 50 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50
  123 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 50 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 50 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 50 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 50 123 (accept_3_4 4 50 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 50 123 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 50 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 123 (Polychromatic418967fa.accept_9_2_5_6_1_536 2
  50 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 123 (accept_3_4 1 50 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 123)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  49 123 (allA_succ_of_accept 48 49 123 (Polychromatic418967fa.accept_9_3_4_6_1_252 48 49 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 123 (accept_3_5 47 49 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 49 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 123
  (Polychromatic418967fa.accept_12_9_1_3_1_350 45 49 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 49 123 (accept_3_5 44 49 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  49 123 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 49 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 49 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 49 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 123 (accept_3_5 41 49 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 49 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 49 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 123
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 49 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 123 (accept_3_5 38 49 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 123 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 49 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 123 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 49 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 123 (accept_3_5 35 49 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 49 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 123
  (Polychromatic418967fa.accept_12_9_1_3_1_350 33 49 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 123 (accept_3_5 32 49 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  49 123 (Polychromatic418967fa.accept_13_5_10_6_1_2361 31 49 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 49 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 123 (accept_3_5 29 49 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 49 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 123
  (Polychromatic418967fa.accept_17_10_15_4_1_5967 27 49 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 123 (accept_3_5 26 49 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 123 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 49 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 123 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 49 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 123 (accept_3_5 23 49 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 49 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 123
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 49 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 123 (accept_3_5 20 49 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  49 123 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 49 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 49 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 49 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 123 (accept_3_5 17 49 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 49 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 123
  (Polychromatic418967fa.accept_13_2_10_6_1_1676 15 49 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 123 (accept_3_5 14 49 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  49 123 (Polychromatic418967fa.accept_21_13_7_18_1_5966 13 49 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 123 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 49 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 123 (accept_3_5 11 49 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 49 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 123
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 49 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 123 (accept_3_5 8 49 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49
  123 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 49 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 49 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 49 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 123 (accept_3_5 5 49 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 49 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 49 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 123 (Polychromatic418967fa.accept_9_3_4_6_1_252 3
  49 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 123 (accept_3_5 2 49 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 123 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 49
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49
  123))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 123 (allA_succ_of_accept 47 48 123
  (Polychromatic418967fa.accept_7_5_6_4_1_117 47 48 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 48 123 (Polychromatic418967fa.accept_9_1_3_6_1_70 46 48 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 48 123 3 15 16 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 48 123 (Polychromatic418967fa.accept_7_2_6_4_1_29 44
  48 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 123
  (Polychromatic418967fa.accept_9_7_3_6_1_270 43 48 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 48 123 3 14 16 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 48 123 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 48 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 123 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 48 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 48 123 3 13 16 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 48 123
  (Polychromatic418967fa.accept_7_3_6_4_1_30 38 48 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 48 123 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 48 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 123 3 12 16 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 123 (Polychromatic418967fa.accept_9_8_3_6_1_533 35
  48 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 48 123
  (Polychromatic418967fa.accept_9_7_3_6_1_270 34 48 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 48 123 3 11 16 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 48 123 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 48 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 123 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 48 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 123 3 10 16 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 123
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 48 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 48 123 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 48 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 48 123 3 9 16 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 48 123 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 48 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 123
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 48 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 48 123 3 8 16 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 48 123 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 48 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 48 123 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 48 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 48 123 3 7 16 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 48 123
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 48 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 48 123 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 48 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 123 3 6 16 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 123 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 48 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 48 123
  (Polychromatic418967fa.accept_7_2_6_4_1_29 16 48 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 48 123 3 5 16 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 48 123 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 48 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 123 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 48 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 123 3 4 16 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 123
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 48 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 48 123 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 48 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 48 123 3 3 16 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 48 123 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 48 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 123
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 48 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 48 123 3 2 16 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 48 123 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 48 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48 123 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 48 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 48 123 3 1 16 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 48 123
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 48 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 48 123 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 48 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 48 123)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 123
  (allA_succ_of_accept 46 47 123 (accept_3_4 46 47 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  47 123 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 47 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 47 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 47 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 123 (accept_3_4 43 47 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 47 123 (Polychromatic418967fa.accept_15_12_2_3_1_1146 42 47 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 123
  (Polychromatic418967fa.accept_7_6_5_4_1_297 41 47 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 123 (accept_3_4 40 47 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  47 123 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 47 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 47 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 47 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 123 (accept_3_4 37 47 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 123 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 47 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 123
  (Polychromatic418967fa.accept_9_8_2_6_1_875 35 47 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 123 (accept_3_4 34 47 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 123 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 47 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 47 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 123 (accept_3_4 31 47 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 123 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 47 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 123
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 47 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 123 (accept_3_4 28 47 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 123 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 47 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 47 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 123 (accept_3_4 25 47 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 123 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 47 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 123
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 47 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 123 (accept_3_4 22 47 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 123 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 47 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 47 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 123 (accept_3_4 19 47 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 123 (Polychromatic418967fa.accept_30_18_17_3_1_5965 18 47 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 123
  (Polychromatic418967fa.accept_9_8_2_6_1_875 17 47 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 123 (accept_3_4 16 47 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 123 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 47 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 47 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 123 (accept_3_4 13 47 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 123 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 47 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 123
  (Polychromatic418967fa.accept_13_11_8_6_1_1023 11 47 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 123 (accept_3_4 10 47 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 123 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 47 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 47 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 123 (accept_3_4 7 47 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 123 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 47 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 123
  (Polychromatic418967fa.accept_9_5_2_6_1_265 5 47 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 123 (accept_3_4 4 47 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  123 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 47 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 47 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 123 (accept_3_4 1 47 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 123))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 123 (allA_succ_of_accept 45
  46 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 46 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 46 123 (accept_3_5 44 46 123 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 46 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 46 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 46 123 (Polychromatic418967fa.accept_12_6_10_3_1_1313 42 46
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 123 (accept_3_5 41 46 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 123 (Polychromatic418967fa.accept_9_4_1_6_1_284 40
  46 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 46 123
  (Polychromatic418967fa.accept_9_3_1_6_1_86 39 46 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 46 123 (accept_3_5 38 46 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  46 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 46 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 46 123 (Polychromatic418967fa.accept_14_8_4_11_1_3035 36 46 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 123 (accept_3_5 35 46 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 123 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 46 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 46 123
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 46 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 46 123 (accept_3_5 32 46 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  46 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 46 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 46 123 (Polychromatic418967fa.accept_9_3_1_6_1_86 30 46 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 123 (accept_3_5 29 46 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 123 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 46 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 46 123
  (Polychromatic418967fa.accept_10_7_6_3_1_927 27 46 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 46 123 (accept_3_5 26 46 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  46 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 46 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 46 123 (Polychromatic418967fa.accept_17_7_12_4_1_2524 24 46 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 123 (accept_3_5 23 46 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 123 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 46 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 123
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 46 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 46 123 (accept_3_5 20 46 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  46 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 46 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 46 123 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 46 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 123 (accept_3_5 17 46 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 123 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 46 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 123
  (Polychromatic418967fa.accept_14_1_4_11_1_3036 15 46 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 46 123 (accept_3_5 14 46 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  46 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 46 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 46 123 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 46 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 123 (accept_3_5 11 46 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 123 (Polychromatic418967fa.accept_22_10_2_13_1_5964 10 46 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 46 123
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 46 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 46 123 (accept_3_5 8 46 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 46
  123 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 46 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 46 123 (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 46 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 123 (accept_3_5 5 46 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 46 123 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 46 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 123 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 46
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 123 (accept_3_5 2 46 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 46
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  123)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 123 (allA_succ_of_accept 44 45 123
  (Polychromatic418967fa.accept_17_10_11_4_1_2522 44 45 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 123 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 45 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 45 123 3 14 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 45 123 (Polychromatic418967fa.accept_7_6_3_4_1_294 41
  45 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 123
  (Polychromatic418967fa.accept_16_8_13_11_1_4772 40 45 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 45 123 3 13 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 45 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 45 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 123 (Polychromatic418967fa.accept_10_7_5_3_1_542 37 45 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 45 123 3 12 15 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 45 123
  (Polychromatic418967fa.accept_12_11_9_3_1_792 35 45 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 45 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 45 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 45 123 3 11 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 45 123 (Polychromatic418967fa.accept_10_2_5_3_1_1408
  32 45 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 123
  (Polychromatic418967fa.accept_12_7_9_3_1_767 31 45 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 45 123 3 10 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 45 123 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 45 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 123 (Polychromatic418967fa.accept_10_8_5_3_1_543 28 45 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 45 123 3 9 15 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 45 123
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 45 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 123 (Polychromatic418967fa.accept_11_3_1_2_1_1063 25 45 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 45 123 3 8 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 123 (Polychromatic418967fa.accept_12_11_9_3_1_792 23 45 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 123
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 45 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 45 123 3 7 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 45 123 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 45 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 123 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 45 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 45 123 3 6 15 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 45 123
  (Polychromatic418967fa.accept_10_7_5_3_1_542 17 45 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 45 123 (Polychromatic418967fa.accept_18_16_9_15_1_4614 16 45 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 123 3 5 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 45 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 123
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 45 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 45 123 3 4 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 45 123 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 45 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 45 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 45 123 3 3 15 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 45 123
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 45 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 123 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 45 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 123 3 2 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 45 123 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 45 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 123
  (Polychromatic418967fa.accept_18_4_9_15_1_3383 4 45 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 45 123 3 1 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 45 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 45 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 123 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 45 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  123))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 123 (allA_succ_of_accept 43 44 123 (accept_3_4 43 44
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 44 123
  (Polychromatic418967fa.accept_12_6_8_3_1_82 42 44 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 44 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 44 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 123 (accept_3_4 40 44 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 44 123 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 44 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 123 (Polychromatic418967fa.accept_9_2_8_6_1_79 38
  44 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 44 123 (accept_3_4 37 44
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 44 123
  (Polychromatic418967fa.accept_13_10_5_6_1_1671 36 44 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 44 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 44 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 123 (accept_3_4 34 44 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 44 123 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 44 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 123 (Polychromatic418967fa.accept_9_5_8_6_1_281 32
  44 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 44 123 (accept_3_4 31 44
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 44 123 (Polychromatic418967fa.accept_9_3_8_6_1_80
  30 44 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 44 123
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 44 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 44 123 (accept_3_4 28 44 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  44 123 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 44 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 44 123 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 44 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 44 123 (accept_3_4 25 44 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 44 123 (Polychromatic418967fa.accept_13_11_5_6_1_519 24 44 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 44 123
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 44 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 44 123 (accept_3_4 22 44 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  44 123 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 44 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 44 123 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 44 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 44 123 (accept_3_4 19 44 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 44 123 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 44 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 44 123
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 44 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 44 123 (accept_3_4 16 44 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  44 123 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 44 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 44 123 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 44 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 44 123 (accept_3_4 13 44 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 44 123 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 44 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 44 123
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 44 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 44 123 (accept_3_4 10 44 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  44 123 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 44 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 44 123 (Polychromatic418967fa.accept_16_8_12_11_1_3697 8 44 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 44 123 (accept_3_4 7 44 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 44 123 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 44 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 44 123
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 44 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 44 123 (accept_3_4 4 44 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 44
  123 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 44 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 44 123 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 44 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 123 (accept_3_4 1 44 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 44 123)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 123 (allA_succ_of_accept 42 43
  123 (Polychromatic418967fa.accept_15_12_13_3_1_1915 42 43 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 43 123 (accept_3_5 41 43 123 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 43 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 43 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 123 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 43 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 123 (accept_3_5 38 43 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 123 (Polychromatic418967fa.accept_9_1_7_6_1_75 37
  43 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 123
  (Polychromatic418967fa.accept_13_10_4_6_1_3224 36 43 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 123 (accept_3_5 35 43 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 43 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 123 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 43 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 123 (accept_3_5 32 43 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 123 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 43 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 123
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 43 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 123 (accept_3_5 29 43 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 43 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 123 (Polychromatic418967fa.accept_15_12_13_3_1_1915 27 43 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 123 (accept_3_5 26 43 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 123 (Polychromatic418967fa.accept_15_10_13_3_1_4816 25 43
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 123
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 43 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 123 (accept_3_5 23 43 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 43 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 123 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 43 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 123 (accept_3_5 20 43 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 123 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 43 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 123
  (Polychromatic418967fa.accept_13_5_4_6_1_2371 18 43 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 123 (accept_3_5 17 43 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 43 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 123 (Polychromatic418967fa.accept_13_2_4_6_1_2356 15 43 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 123 (accept_3_5 14 43 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 123 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 43 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 123
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 43 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 123 (accept_3_5 11 43 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 43 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 123 (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 43 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 123 (accept_3_5 8 43 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 123 (Polychromatic418967fa.accept_13_7_4_6_1_3221 7 43 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 123
  (Polychromatic418967fa.accept_25_6_18_23_1_5963 6 43 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 123 (accept_3_5 5 43 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  123 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 43 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 123 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 43 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 123 (accept_3_5 2 43 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 123 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 43 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 123))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 123
  (allA_succ_of_accept 41 42 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 42 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 42 123 (Polychromatic418967fa.accept_11_7_9_2_1_260 40 42 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 42 123 3 13 14 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 42 123
  (Polychromatic418967fa.accept_12_2_6_3_1_331 38 42 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 42 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 42 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 123 3 12 14 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 123 (Polychromatic418967fa.accept_10_5_2_3_1_239 35
  42 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 42 123
  (Polychromatic418967fa.accept_12_10_6_3_1_786 34 42 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 42 123 3 11 14 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 42 123 (Polychromatic418967fa.accept_12_8_6_3_1_366 32 42 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 123 (Polychromatic418967fa.accept_10_1_2_3_1_1910 31 42 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 123 3 10 14 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 123
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 42 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 42 123 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 42 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 42 123 3 9 14 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 42 123 (Polychromatic418967fa.accept_11_4_9_2_1_259 26 42 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 123
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 42 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 123 3 8 14 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 42 123 (Polychromatic418967fa.accept_13_10_3_6_1_1003 23 42 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 42 123 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 42 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 42 123 3 7 14 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 42 123
  (Polychromatic418967fa.accept_12_8_6_3_1_366 20 42 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 42 123 (Polychromatic418967fa.accept_20_19_2_3_1_4486 19 42 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 123 3 6 14 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 42 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 42 123
  (Polychromatic418967fa.accept_12_4_6_3_1_332 16 42 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 42 123 3 5 14 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 42 123 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 42 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 42 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 123 3 4 14 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 123
  (Polychromatic418967fa.accept_10_1_2_3_1_1910 11 42 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 42 123 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 42 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 42 123 3 3 14 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 42 123 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 42 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 123
  (Polychromatic418967fa.accept_11_7_9_2_1_260 7 42 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 42 123 3 2 14 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 42 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 42 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42 123 (Polychromatic418967fa.accept_11_4_9_2_1_259 4 42 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 42 123 3 1 14 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 42 123
  (Polychromatic418967fa.accept_12_2_6_3_1_331 2 42 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 42 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 42 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 42 123)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 123
  (allA_succ_of_accept 40 41 123 (accept_3_4 40 41 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  41 123 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 41 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 41 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 41 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 123 (accept_3_4 37 41 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 41 123 (Polychromatic418967fa.accept_13_10_2_6_1_1044 36 41 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 123
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 41 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 123 (accept_3_4 34 41 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 123 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 41 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 41 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 123 (accept_3_4 31 41 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 41 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 123
  (Polychromatic418967fa.accept_9_2_5_6_1_536 29 41 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 123 (accept_3_4 28 41 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 123 (Polychromatic418967fa.accept_11_5_8_2_1_588 27 41 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 41 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 123 (accept_3_4 25 41 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 123 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 41 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 123
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 41 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 123 (accept_3_4 22 41 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 123 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 41 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 41 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 123 (accept_3_4 19 41 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 41 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 123
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 41 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 123 (accept_3_4 16 41 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 123 (Polychromatic418967fa.accept_19_15_3_9_1_5962 15 41 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 41 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 123 (accept_3_4 13 41 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 123 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 41 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 123
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 41 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 123 (accept_3_4 10 41 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 123 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 41 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 41 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 123 (accept_3_4 7 41 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 41 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 123
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 41 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 123 (accept_3_4 4 41 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  123 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 41 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 41 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 123 (accept_3_4 1 41 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 123))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 123 (allA_succ_of_accept 39 40 123
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 40 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 123 (accept_3_5 38 40 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  40 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 40 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 40 123 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 40 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 40 123 (accept_3_5 35 40 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 40 123 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 40 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 123
  (Polychromatic418967fa.accept_13_7_1_6_1_3287 33 40 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 40 123 (accept_3_5 32 40 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  40 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 40 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 40 123 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 40 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 40 123 (accept_3_5 29 40 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 40 123 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 40 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 123
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 40 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 40 123 (accept_3_5 26 40 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  40 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 40 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 40 123 (Polychromatic418967fa.accept_15_9_10_3_1_2845 24 40 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 123 (accept_3_5 23 40 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 123 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 40 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 123
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 40 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 40 123 (accept_3_5 20 40 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  40 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 40 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 40 123 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 40 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 123 (accept_3_5 17 40 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 40 123 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 40 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 40 123
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 40 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 40 123 (accept_3_5 14 40 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  40 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 40 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 40 123 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 40 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 40 123 (accept_3_5 11 40 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 40 123 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 40 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 40 123
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 40 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 40 123 (accept_3_5 8 40 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40
  123 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 40 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 40 123 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 40 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 40 123 (accept_3_5 5 40 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 40 123 (Polychromatic418967fa.accept_16_4_8_11_1_5961 4 40 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 123 (Polychromatic418967fa.accept_9_3_4_6_1_252 3
  40 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 40 123 (accept_3_5 2 40 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 40
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  123)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 123 (allA_succ_of_accept 38 39 123
  (Polychromatic418967fa.accept_9_2_3_6_1_88 38 39 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 123 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 39 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 123 3 12 13 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 123 (Polychromatic418967fa.accept_9_8_3_6_1_533 35
  39 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 123
  (Polychromatic418967fa.accept_9_7_3_6_1_270 34 39 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 39 123 3 11 13 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 39 123 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 39 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 123 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 39 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 123 3 10 13 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 123
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 39 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 123 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 39 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 123 3 9 13 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 123 (Polychromatic418967fa.accept_9_8_3_6_1_533 26 39 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 123
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 39 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 39 123 3 8 13 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 39 123 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 39 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 123 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 39 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 123 3 7 13 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 123
  (Polychromatic418967fa.accept_8_4_7_3_1_144 20 39 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 123 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 39 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 123 3 6 13 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 123 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 39 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 123
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 39 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 39 123 3 5 13 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 39 123 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 39 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 123 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 39 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 39 123 3 4 13 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 39 123
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 39 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 123 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 39 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 123 3 3 13 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 123 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 39 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 123
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 39 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 39 123 3 2 13 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 39 123 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 39 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 123 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 39 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 39 123 3 1 13 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 39 123
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 39 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 123 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 39 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 39 123))))))))))))))))))))))))))))))))))))))) (allB_succ 38 123
  (allA_succ_of_accept 37 38 123 (accept_3_4 37 38 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 123 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 38 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 38 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 123 (accept_3_4 34 38 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 38 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 123
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 38 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 123 (accept_3_4 31 38 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 123 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 38 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 38 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 123 (accept_3_4 28 38 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 123 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 38 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 123
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 38 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 123 (accept_3_4 25 38 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 123 (Polychromatic418967fa.accept_15_9_8_3_1_557 24 38 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 38 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 123 (accept_3_4 22 38 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 38 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 123
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 38 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 123 (accept_3_4 19 38 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 123 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 38 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 38 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 123 (accept_3_4 16 38 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 123 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 38 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 123
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 38 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 123 (accept_3_4 13 38 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 123 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 38 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 38 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 123 (accept_3_4 10 38 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 38 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 123
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 38 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 123 (accept_3_4 7 38 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  123 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 38 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 38 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 123 (accept_3_4 4 38 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 123 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 38 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 123 (Polychromatic418967fa.accept_13_2_12_6_1_2394
  2 38 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 123 (accept_3_4 1 38
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 123)))))))))))))))))))))))))))))))))))))) (allB_succ 37 123
  (allA_succ_of_accept 36 37 123 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 37 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 123 (accept_3_5 35 37 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 37 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 37 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 123 (Polychromatic418967fa.accept_7_5_2_4_1_126 33
  37 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 123 (accept_3_5 32 37
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 123
  (Polychromatic418967fa.accept_9_4_1_6_1_284 31 37 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 37 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 37 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 123 (accept_3_5 29 37 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 37 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 37 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 123 (Polychromatic418967fa.accept_7_6_2_4_1_291 27
  37 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 123 (accept_3_5 26 37
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 123
  (Polychromatic418967fa.accept_9_7_1_6_1_261 25 37 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 37 123 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 37 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 123 (accept_3_5 23 37 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 37 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 37 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 123 (Polychromatic418967fa.accept_9_3_1_6_1_86 21
  37 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 123 (accept_3_5 20 37
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 123
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 37 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 37 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 37 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 123 (accept_3_5 17 37 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 37 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 37 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 123 (Polychromatic418967fa.accept_10_5_7_3_1_561
  15 37 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 123 (accept_3_5 14
  37 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 123
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 37 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 37 123 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 37 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 123 (accept_3_5 11 37 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 37 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 37 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 123 (Polychromatic418967fa.accept_11_9_4_2_1_600 9
  37 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 123 (accept_3_5 8 37 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 123 (Polychromatic418967fa.accept_9_7_1_6_1_261 7
  37 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 123
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 37 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 123 (accept_3_5 5 37 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  123 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 37 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 123 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 37 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 123 (accept_3_5 2 37 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 123 (Polychromatic418967fa.accept_25_1_12_23_1_5960 1 37 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 123))))))))))))))))))))))))))))))))))))) (allB_succ 36 123
  (allA_succ_of_accept 35 36 123 (Polychromatic418967fa.accept_13_9_10_6_1_1028 35 36 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 36 123 (Polychromatic418967fa.accept_11_1_3_2_1_1090 34 36 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 36 123 3 11 12 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 36 123
  (Polychromatic418967fa.accept_14_4_8_11_1_794 32 36 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 36 123 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 36 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 123 3 10 12 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 123 (Polychromatic418967fa.accept_10_9_6_3_1_545 29
  36 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 123
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 36 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 36 123 3 9 12 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 36 123 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 36 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 123 (Polychromatic418967fa.accept_13_12_10_6_1_3212 25 36
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 123 3 8 12 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 123
  (Polychromatic418967fa.accept_8_7_4_3_1_156 23 36 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 36 123 (Polychromatic418967fa.accept_13_9_10_6_1_1028 22 36 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 36 123 3 7 12 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 36 123 (Polychromatic418967fa.accept_15_5_6_3_1_525 20 36 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 123
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 36 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 123 3 6 12 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 123 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 36 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 36 123 (Polychromatic418967fa.accept_13_3_10_6_1_2382 16 36
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 36 123 3 5 12 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 36 123
  (Polychromatic418967fa.accept_19_14_17_9_1_5959 14 36 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 36 123 (Polychromatic418967fa.accept_19_13_17_9_1_3312 13 36 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 123 3 4 12 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 123 (Polychromatic418967fa.accept_15_11_6_3_1_1192 11 36 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 36 123
  (Polychromatic418967fa.accept_7_3_1_4_1_121 10 36 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 36 123 3 3 12 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 36 123 (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 36 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 123 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 36 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 123 3 2 12 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 123
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 36 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 36 123 (Polychromatic418967fa.accept_13_4_10_6_1_989 4 36 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 36 123 3 1 12 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 36 123 (Polychromatic418967fa.accept_13_2_10_6_1_1676 2 36 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 123
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 36 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 36 123)))))))))))))))))))))))))))))))))))) (allB_succ 35 123 (allA_succ_of_accept 34 35 123 (accept_3_4 34
  35 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 123
  (Polychromatic418967fa.accept_12_9_11_3_1_772 33 35 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 35 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 123 (accept_3_4 31 35 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 123 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 35 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 123 (Polychromatic418967fa.accept_9_2_8_6_1_79 29
  35 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 123 (accept_3_4 28 35
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 123
  (Polychromatic418967fa.accept_10_7_5_3_1_542 27 35 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 35 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 35 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 123 (accept_3_4 25 35 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 35 123 (Polychromatic418967fa.accept_14_10_7_11_1_3015 24 35 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 123
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 35 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 123 (accept_3_4 22 35 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  35 123 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 35 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 35 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 35 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 123 (accept_3_4 19 35 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 123 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 35 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 123
  (Polychromatic418967fa.accept_10_7_5_3_1_542 17 35 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 35 123 (accept_3_4 16 35 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  35 123 (Polychromatic418967fa.accept_13_2_9_6_1_501 15 35 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 35 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 35 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 123 (accept_3_4 13 35 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 123 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 35 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 123
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 35 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 35 123 (accept_3_4 10 35 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  35 123 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 35 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 35 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 35 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 123 (accept_3_4 7 35 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 123 (Polychromatic418967fa.accept_15_6_5_3_1_1988 6 35 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 123
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 35 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 35 123 (accept_3_4 4 35 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35
  123 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 35 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 35 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 35 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 123 (accept_3_4 1 35 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 35 123))))))))))))))))))))))))))))))))))) (allB_succ 34 123 (allA_succ_of_accept 33 34 123
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 34 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 34 123 (accept_3_5 32 34 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  34 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 34 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 34 123 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 34 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 123 (accept_3_5 29 34 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 123 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 34 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 123
  (Polychromatic418967fa.accept_10_7_4_3_1_560 27 34 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 123 (accept_3_5 26 34 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 34 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 123 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 34 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 123 (accept_3_5 23 34 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 123 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 34 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 123
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 34 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 123 (accept_3_5 20 34 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 34 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 123 (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 34 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 123 (accept_3_5 17 34 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 123 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 34 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 123
  (Polychromatic418967fa.accept_13_2_8_6_1_2390 15 34 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 123 (accept_3_5 14 34 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 34 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 123 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 34 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 123 (accept_3_5 11 34 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 123 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 34 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 123
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 34 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 123 (accept_3_5 8 34 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  123 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 34 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 34 123 (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 34 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 123 (accept_3_5 5 34 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 34 123 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 34 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 123 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 34
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 123 (accept_3_5 2 34 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 34
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 123))))))))))))))))))))))))))))))))))
  (allB_succ 33 123 (allA_succ_of_accept 32 33 123 (Polychromatic418967fa.accept_17_15_16_4_1_2418 32 33 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 123
  (Polychromatic418967fa.accept_12_7_9_3_1_767 31 33 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 33 123 3 10 11 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 33 123 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 33 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 123 (Polychromatic418967fa.accept_16_12_1_11_1_5958 28 33
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 33 123 3 9 11 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 33 123
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 33 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 123 (Polychromatic418967fa.accept_12_1_9_3_1_370 25 33 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 123 3 8 11 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 123 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 33 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 123
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 33 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 33 123 3 7 11 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 33 123 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 33 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 123 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 33 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 33 123 3 6 11 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 33 123
  (Polychromatic418967fa.accept_12_5_9_3_1_85 17 33 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 123 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 33 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 123 3 5 11 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 33 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 123
  (Polychromatic418967fa.accept_7_6_5_4_1_297 13 33 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 33 123 3 4 11 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 33 123 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 33 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 33 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 33 123 3 3 11 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 33 123
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 33 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 123 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 33 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 123 3 2 11 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 123 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 33 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 123
  (Polychromatic418967fa.accept_13_4_7_6_1_2359 4 33 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 33 123 3 1 11 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 33 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 33 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 123 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 33 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 123)))))))))))))))))))))))))))))))))
  (allB_succ 32 123 (allA_succ_of_accept 31 32 123 (accept_3_4 31 32 123 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 32 123 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 32 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 32 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 32 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 123 (accept_3_4 28 32 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 32 123 (Polychromatic418967fa.accept_15_12_2_3_1_1146
  27 32 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 123
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 32 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 32 123 (accept_3_4 25 32 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  32 123 (Polychromatic418967fa.accept_19_5_13_9_1_5957 24 32 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 32 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 32 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 123 (accept_3_4 22 32 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 32 123 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 32 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 123
  (Polychromatic418967fa.accept_9_2_5_6_1_536 20 32 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 32 123 (accept_3_4 19 32 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  32 123 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 32 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 32 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 32 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 123 (accept_3_4 16 32 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 32 123 (Polychromatic418967fa.accept_10_5_2_3_1_239 15 32 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 123
  (Polychromatic418967fa.accept_15_14_2_3_1_1980 14 32 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 32 123 (accept_3_4 13 32 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  32 123 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 32 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 32 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 32 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 123 (accept_3_4 10 32 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 123 (Polychromatic418967fa.accept_20_9_12_3_1_3191 9 32 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 123
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 32 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 123 (accept_3_4 7 32 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32
  123 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 32 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 32 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 32 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 123 (accept_3_4 4 32 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 32 123 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 32 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 123 (Polychromatic418967fa.accept_9_2_5_6_1_536 2
  32 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 123 (accept_3_4 1 32 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 123)))))))))))))))))))))))))))))))) (allB_succ 31 123
  (allA_succ_of_accept 30 31 123 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 31 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 123 (accept_3_5 29 31 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 31 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 123 (Polychromatic418967fa.accept_7_6_3_4_1_294 27
  31 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 123 (accept_3_5 26 31
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 123
  (Polychromatic418967fa.accept_9_7_4_6_1_273 25 31 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 31 123 (Polychromatic418967fa.accept_13_11_5_6_1_519 24 31 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 123 (accept_3_5 23 31 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 31 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 31 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 123 (Polychromatic418967fa.accept_9_3_4_6_1_252 21
  31 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 123 (accept_3_5 20 31
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 123 (Polychromatic418967fa.accept_9_1_4_6_1_5
  19 31 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 123
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 31 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 123 (accept_3_5 17 31 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 31 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 123 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 31 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 123 (accept_3_5 14 31 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 123 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 31 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 123
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 31 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 123 (accept_3_5 11 31 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 31 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 123 (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 31 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 123 (accept_3_5 8 31 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 123 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 31 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 123
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 31 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 123 (accept_3_5 5 31 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  123 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 31 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 123 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 31 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 123 (accept_3_5 2 31 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 123 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 31 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 123))))))))))))))))))))))))))))))) (allB_succ 30 123
  (allA_succ_of_accept 29 30 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 30 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 30 123 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 30 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 30 123 3 9 10 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 30 123
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 30 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 30 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 30 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 123 3 8 10 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 123 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 30 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 123
  (Polychromatic418967fa.accept_9_4_3_6_1_532 22 30 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 30 123 3 7 10 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 30 123 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 30 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 123 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 30 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 123 3 6 10 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 123
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 30 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 30 123 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 30 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 30 123 3 5 10 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 30 123 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 30 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 123
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 30 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 30 123 3 4 10 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 30 123 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 30 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 30 123 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 30 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 30 123 3 3 10 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 30 123
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 30 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 30 123 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 30 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 123 3 2 10 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 30 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30 123
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 30 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 30 123 3 1 10 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 30 123 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 30 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 30 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 123)))))))))))))))))))))))))))))) (allB_succ
  29 123 (allA_succ_of_accept 28 29 123 (accept_3_4 28 29 123 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 29 123 (Polychromatic418967fa.accept_13_1_3_6_1_158 27 29 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 29 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 123 (accept_3_4 25 29 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 29 123 (Polychromatic418967fa.accept_7_3_1_4_1_121 24
  29 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 123
  (Polychromatic418967fa.accept_9_5_2_6_1_265 23 29 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 123 (accept_3_4 22 29 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 123 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 29 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 29 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 123 (accept_3_4 19 29 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 29 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 123
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 29 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 123 (accept_3_4 16 29 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 123 (Polychromatic418967fa.accept_19_15_10_9_1_5956 15 29 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 29 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 123 (accept_3_4 13 29 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 123 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 29 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 123
  (Polychromatic418967fa.accept_15_11_14_3_1_1965 11 29 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 123 (accept_3_4 10 29 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 123 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 29 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 29 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 123 (accept_3_4 7 29 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 29 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 123
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 29 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 123 (accept_3_4 4 29 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  123 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 29 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 29 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 123 (accept_3_4 1 29 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 123))))))))))))))))))))))))))))) (allB_succ 28 123 (allA_succ_of_accept 27 28 123
  (Polychromatic418967fa.accept_13_1_2_6_1_515 27 28 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 28 123 (accept_3_5 26 28 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  28 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 28 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 28 123 (Polychromatic418967fa.accept_15_9_13_3_1_535 24 28 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 123 (accept_3_5 23 28 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 123 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 28 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 28 123
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 28 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 28 123 (accept_3_5 20 28 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  28 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 28 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 28 123 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 28 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 28 123 (accept_3_5 17 28 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 28 123 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 28 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 28 123
  (Polychromatic418967fa.accept_8_7_4_3_1_156 15 28 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 28 123 (accept_3_5 14 28 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  28 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 28 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 28 123 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 28 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 28 123 (accept_3_5 11 28 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 28 123 (Polychromatic418967fa.accept_13_10_2_6_1_1044 10 28 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 28 123
  (Polychromatic418967fa.accept_13_9_2_6_1_514 9 28 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 28 123 (accept_3_5 8 28 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 28
  123 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 28 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 28 123 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 28 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 28 123 (accept_3_5 5 28 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 28 123 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 28 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 28 123 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 28
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 123 (accept_3_5 2 28 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 28 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 28
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 123))))))))))))))))))))))))))))
  (allB_succ 27 123 (allA_succ_of_accept 26 27 123 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 27 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 123
  (Polychromatic418967fa.accept_10_5_7_3_1_561 25 27 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 27 123 3 8 9 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 27 123 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 27 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 123 (Polychromatic418967fa.accept_13_9_1_6_1_510 22 27 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 27 123 3 7 9 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 27 123
  (Polychromatic418967fa.accept_13_7_1_6_1_3287 20 27 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 123 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 27 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 27 123 3 6 9 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 27 123 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 27 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 123
  (Polychromatic418967fa.accept_7_2_6_4_1_29 16 27 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 27 123 3 5 9 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 27 123 (Polychromatic418967fa.accept_10_4_7_3_1_54 14 27 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 123 (Polychromatic418967fa.accept_15_13_12_3_1_1180 13 27
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 27 123 3 4 9 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 27 123
  (Polychromatic418967fa.accept_17_11_10_4_1_5955 11 27 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 27 123 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 27 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 27 123 3 3 9 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 27 123 (Polychromatic418967fa.accept_11_8_5_2_1_1629 8 27 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 123
  (Polychromatic418967fa.accept_13_7_1_6_1_3287 7 27 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 27 123 3 2 9 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 27 123 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 27 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 123 (Polychromatic418967fa.accept_10_4_7_3_1_54 4 27 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 27 123 3 1 9 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 27 123
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 27 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 27 123 (Polychromatic418967fa.accept_19_1_8_9_1_3304 1 27 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 27 123))))))))))))))))))))))))))) (allB_succ 26 123 (allA_succ_of_accept 25
  26 123 (accept_3_4 25 26 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 123
  (Polychromatic418967fa.accept_19_5_7_9_1_5954 24 26 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 26 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 26 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 123 (accept_3_4 22 26 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 26 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 26 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 123 (Polychromatic418967fa.accept_7_6_5_4_1_297 20
  26 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 123 (accept_3_4 19 26
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 26 123
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 26 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 26 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 26 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 123 (accept_3_4 16 26 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 26 123 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 26 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 123 (Polychromatic418967fa.accept_9_5_8_6_1_281 14
  26 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 26 123 (accept_3_4 13 26
  123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 26 123 (Polychromatic418967fa.accept_9_3_8_6_1_80
  12 26 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 26 123
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 26 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 26 123 (accept_3_4 10 26 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  26 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 26 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 26 123 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 26 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 26 123 (accept_3_4 7 26 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 26 123 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 26 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 26 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 26
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 123 (accept_3_4 4 26 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 26 123 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 26
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 123
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 26 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 26 123 (accept_3_4 1 26 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  123)))))))))))))))))))))))))) (allB_succ 25 123 (allA_succ_of_accept 24 25 123
  (Polychromatic418967fa.accept_15_9_10_3_1_2845 24 25 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 123 (accept_3_5 23 25 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 25 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 123 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 25 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 123 (accept_3_5 20 25 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 123 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 25 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 123
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 25 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 123 (accept_3_5 17 25 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 25 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 123 (Polychromatic418967fa.accept_13_2_12_6_1_2394 15 25 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 123 (accept_3_5 14 25 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 123 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 25 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 123
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 25 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 123 (accept_3_5 11 25 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 25 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 123 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 25 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 123 (accept_3_5 8 25 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 123 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 25 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 123
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 25 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 123 (accept_3_5 5 25 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  123 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 25 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 25 123 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 25 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 123 (accept_3_5 2 25 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 25 123 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 25 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 123))))))))))))))))))))))))) (allB_succ 24 123
  (allA_succ_of_accept 23 24 123 (Polychromatic418967fa.accept_15_8_9_3_1_1194 23 24 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 123 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 24 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 24 123 3 7 8 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 24 123
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 24 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 24 123 (Polychromatic418967fa.accept_10_9_4_3_1_539 19 24 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 123 3 6 8 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 123 (Polychromatic418967fa.accept_10_7_4_3_1_560 17 24 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 123
  (Polychromatic418967fa.accept_18_16_6_15_1_3376 16 24 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 24 123 3 5 8 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 24 123 (Polychromatic418967fa.accept_17_14_7_4_1_3476 14 24 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 123 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 24 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 123 3 4 8 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 123
  (Polychromatic418967fa.accept_18_11_6_15_1_5953 11 24 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 24 123 (Polychromatic418967fa.accept_15_10_9_3_1_1947 10 24 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 24 123 3 3 8 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 24 123 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 24 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 123
  (Polychromatic418967fa.accept_10_7_4_3_1_560 7 24 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 24 123 3 2 8 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 24 123 (Polychromatic418967fa.accept_13_5_11_6_1_505 5 24 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 123 (Polychromatic418967fa.accept_13_4_11_6_1_1033 4 24 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 24 123 3 1 8 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 24 123
  (Polychromatic418967fa.accept_21_2_3_18_1_5952 2 24 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 24 123 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 24 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 24 123)))))))))))))))))))))))) (allB_succ 23 123 (allA_succ_of_accept 22 23
  123 (accept_3_4 22 23 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 123
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 23 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 23 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 123 (accept_3_4 19 23 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 123 (Polychromatic418967fa.accept_13_5_10_6_1_2361 18 23 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 123
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 23 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 23 123 (accept_3_4 16 23 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  23 123 (Polychromatic418967fa.accept_13_2_10_6_1_1676 15 23 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 23 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 23 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 123 (accept_3_4 13 23 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 23 123 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 23 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 123
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 23 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 123 (accept_3_4 10 23 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  23 123 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 23 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 23 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 23 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 123 (accept_3_4 7 23 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 123 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 23 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 123
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 23 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 123 (accept_3_4 4 23 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23
  123 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 23 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 23 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 23 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 123 (accept_3_4 1 23 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 23 123))))))))))))))))))))))) (allB_succ 22 123 (allA_succ_of_accept 21 22 123
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 22 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 123 (accept_3_5 20 22 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  22 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 22 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 22 123 (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 22 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 123 (accept_3_5 17 22 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 123 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 22 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 123
  (Polychromatic418967fa.accept_10_5_2_3_1_239 15 22 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 22 123 (accept_3_5 14 22 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  22 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 22 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 22 123 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 22 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 123 (accept_3_5 11 22 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 123 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 22 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 123
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 22 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 22 123 (accept_3_5 8 22 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22
  123 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 22 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 22 123 (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 22 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 123 (accept_3_5 5 22 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 22 123 (Polychromatic418967fa.accept_13_4_9_6_1_2376 4 22 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 123 (Polychromatic418967fa.accept_7_3_1_4_1_121 3
  22 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 123 (accept_3_5 2 22 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 22
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 123)))))))))))))))))))))) (allB_succ 21
  123 (allA_succ_of_accept 20 21 123 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 21 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 123 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 21 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 123 3 6 7 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 123
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 21 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 123 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 21 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 21 123 3 5 7 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 21 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 21 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 123
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 21 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 21 123 3 4 7 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 21 123 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 21 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 21 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 123 3 3 7 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 123
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 21 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 123 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 21 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 21 123 3 2 7 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 21 123 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 21 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 123
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 21 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 21 123 3 1 7 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 21 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 21 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 123 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 21 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 123))))))))))))))))))))) (allB_succ 20 123
  (allA_succ_of_accept 19 20 123 (accept_3_4 19 20 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  20 123 (Polychromatic418967fa.accept_11_7_9_2_1_260 18 20 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 20 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 20 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 123 (accept_3_4 16 20 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 20 123 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 20 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 20 123
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 20 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 20 123 (accept_3_4 13 20 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  20 123 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 20 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 20 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 20 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 20 123 (accept_3_4 10 20 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 20 123 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 20 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 123
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 20 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 20 123 (accept_3_4 7 20 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20
  123 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 20 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 20 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 20 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 20 123 (accept_3_4 4 20 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 20 123 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 20 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 20 123 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 20
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 123 (accept_3_4 1 20 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20 123)))))))))))))))))))) (allB_succ 19 123 (allA_succ_of_accept
  18 19 123 (Polychromatic418967fa.accept_24_18_19_3_1_5951 18 19 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 19 123 (accept_3_5 17 19 123 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 19 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 19 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 19 123 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 19 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 123 (accept_3_5 14 19 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 123 (Polychromatic418967fa.accept_7_6_5_4_1_297 13
  19 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 123
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 19 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 123 (accept_3_5 11 19 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 123 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 19 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 123 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 19 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 123 (accept_3_5 8 19 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 123 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 19 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 123
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 19 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 123 (accept_3_5 5 19 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  123 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 19 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 123 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 19 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 123 (accept_3_5 2 19 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 123 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 19 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 123))))))))))))))))))) (allB_succ 18 123 (allA_succ_of_accept 17
  18 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 18 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 18 123 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 18 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 18 123 3 5 6 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 18 123 (Polychromatic418967fa.accept_12_2_6_3_1_331 14
  18 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 18 123
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 18 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 18 123 3 4 6 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 18 123 (Polychromatic418967fa.accept_10_1_8_3_1_947 11 18 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 123 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 18 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 18 123 3 3 6 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 18 123
  (Polychromatic418967fa.accept_12_8_6_3_1_366 8 18 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 123 (Polychromatic418967fa.accept_14_7_4_11_1_3038 7 18 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 123 3 2 6 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 18 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 123
  (Polychromatic418967fa.accept_12_4_6_3_1_332 4 18 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 18 123 3 1 6 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 18 123 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 18 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 18 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 123)))))))))))))))))) (allB_succ 17 123
  (allA_succ_of_accept 16 17 123 (accept_3_4 16 17 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  17 123 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 17 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 17 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 17 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 123 (accept_3_4 13 17 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 17 123 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 17 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 123
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 17 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 17 123 (accept_3_4 10 17 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  17 123 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 17 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 17 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 17 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 123 (accept_3_4 7 17 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 17 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 17 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 123
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 17 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 17 123 (accept_3_4 4 17 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17
  123 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 17 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 17 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 17 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 123 (accept_3_4 1 17 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 17 123))))))))))))))))) (allB_succ 16 123 (allA_succ_of_accept 15 16 123
  (Polychromatic418967fa.accept_17_15_16_4_1_2418 15 16 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 16 123 (accept_3_5 14 16 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  16 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 16 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 16 123 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 16 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 16 123 (accept_3_5 11 16 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 16 123 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 16 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 16 123
  (Polychromatic418967fa.accept_10_9_6_3_1_545 9 16 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 16 123 (accept_3_5 8 16 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 16
  123 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 16 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 16 123 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 16 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 16 123 (accept_3_5 5 16 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 16 123 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 16 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 16 123 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 16
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 123 (accept_3_5 2 16 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 16 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 16
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 123)))))))))))))))) (allB_succ 15 123
  (allA_succ_of_accept 14 15 123 (Polychromatic418967fa.accept_13_1_2_6_1_515 14 15 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 123 (Polychromatic418967fa.accept_19_13_15_9_1_3293 13 15
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 123 3 4 5 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 123
  (Polychromatic418967fa.accept_17_11_15_4_1_2415 11 15 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 15 123 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 15 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 15 123 3 3 5 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 15 123 (Polychromatic418967fa.accept_10_8_5_3_1_543 8 15 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 123
  (Polychromatic418967fa.accept_10_7_5_3_1_542 7 15 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 15 123 3 2 5 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 15 123 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 15 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 123 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 15 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 123 3 1 5 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 123
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 2 15 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 123 (Polychromatic418967fa.accept_13_1_2_6_1_515 1 15 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 15 123))))))))))))))) (allB_succ 14 123 (allA_succ_of_accept 13 14 123
  (accept_3_4 13 14 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 123
  (Polychromatic418967fa.accept_9_3_5_6_1_253 12 14 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 14 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 14 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 123 (accept_3_4 10 14 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 14 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 14 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 14 123 (Polychromatic418967fa.accept_9_8_5_6_1_538 8
  14 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 123 (accept_3_4 7 14 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 14 123 (Polychromatic418967fa.accept_12_6_2_3_1_354 6
  14 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 123
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 14 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 14 123 (accept_3_4 4 14 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14
  123 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 14 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 14 123 (Polychromatic418967fa.accept_9_2_5_6_1_536 2 14 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 123 (accept_3_4 1 14 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 123)))))))))))))) (allB_succ 13 123 (allA_succ_of_accept 12 13 123
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 13 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 123 (accept_3_5 11 13 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 13 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 123 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 13 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 123 (accept_3_5 8 13 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 123 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 13 123 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 123
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 13 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 123 (accept_3_5 5 13 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  123 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 13 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 123 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 13 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 123 (accept_3_5 2 13 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 123 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 13 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 123))))))))))))) (allB_succ 12 123 (allA_succ_of_accept 11 12
  123 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 12 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 12 123 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 12 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 12 123 3 3 4 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 12 123 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 12 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 123
  (Polychromatic418967fa.accept_8_7_4_3_1_156 7 12 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 12 123 3 2 4 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 12 123 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 12 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 123 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 12 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 12 123 3 1 4 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 12 123
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 12 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 12 123 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 12 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 12 123)))))))))))) (allB_succ 11 123 (allA_succ_of_accept 10 11 123
  (accept_3_4 10 11 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 123
  (Polychromatic418967fa.accept_12_9_11_3_1_772 9 11 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 123 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 11 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 123 (accept_3_4 7 11 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 123 (Polychromatic418967fa.accept_15_6_11_3_1_1172 6 11 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 123 (Polychromatic418967fa.accept_9_5_2_6_1_265 5
  11 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 123 (accept_3_4 4 11 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 123 (Polychromatic418967fa.accept_9_3_2_6_1_264 3
  11 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 123
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 11 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 123 (accept_3_4 1 11 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  123))))))))))) (allB_succ 10 123 (allA_succ_of_accept 9 10 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 10 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 10 123 (accept_3_5 8 10 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 10 123 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 10
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 10 123
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 10 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 10 123 (accept_3_5 5 10 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 10
  123 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 10 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 10 123 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 10 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 123 (accept_3_5 2 10 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 10 123 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 10 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 123)))))))))) (allB_succ 9 123 (allA_succ_of_accept 8 9 123
  (Polychromatic418967fa.accept_15_8_9_3_1_1194 8 9 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 9 123 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 9 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 123 3 2 3 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 123 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 9 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 123
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 4 9 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 9 123 3 1 3 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 9 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 9 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 123 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 9 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 123))))))))) (allB_succ 8 123
  (allA_succ_of_accept 7 8 123 (accept_3_4 7 8 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 123
  (Polychromatic418967fa.accept_10_6_8_3_1_930 6 8 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 8 123 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 8 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 8 123 (accept_3_4 4 8 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 8 123 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 8 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 8 123 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 8
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 123 (accept_3_4 1 8 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 123)))))))) (allB_succ 7 123 (allA_succ_of_accept 6 7 123
  (Polychromatic418967fa.accept_10_6_7_3_1_547 6 7 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 123 (accept_3_5 5 7 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 123
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 7 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 123 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 7 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 123 (accept_3_5 2 7 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 123 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 7 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 123))))))) (allB_succ 6 123 (allA_succ_of_accept 5 6 123
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 6 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 123 (Polychromatic418967fa.accept_11_4_6_2_1_51 4 6 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 6 123 3 1 2 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 6 123 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 6 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 123
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 6 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 6 123)))))) (allB_succ 5 123 (allA_succ_of_accept 4 5 123 (accept_3_4 4 5 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 5 123 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 5 123 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 123 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 5
  123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 123 (accept_3_4 1 5 123
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 123))))) (allB_succ 4 123 (allA_succ_of_accept 3 4 123
  (Polychromatic418967fa.accept_9_3_4_6_1_252 3 4 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 123 (accept_3_5 2 4 123 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 123
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 4 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 123)))) (allB_succ 3 123 (allA_succ_of_accept 2 3 123 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 3 123
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 123
  (Polychromatic418967fa.accept_7_1_3_4_1_128 1 3 123 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 3 123))) (allB_succ 2 123 (allA_succ_of_accept 1 2 123 (accept_3_4 1 2 123 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 2 123)) (allB_two
  123)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


