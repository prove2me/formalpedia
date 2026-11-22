-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch87
-- name    : Polychromatic418967fa_Branch87
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:09:23.735995+00:00
-- url     : https://prove2.me/theorems/c8822735-305f-4c8f-b398-36fb4818445f
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

def Polychromatic418967fa.branch_87 : allB 87 87 :=
  allB_succ' 2 86 87 (Eq.refl Bool.true) (allA_succ_of_accept 1 86 87 (accept_3_4 1 86 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 86 87)) (allB_succ' 3 85 87 (Eq.refl Bool.true) (allA_succ_of_accept 2 85 87 (accept_3_5 2 85 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 87 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 85
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85 87))) (allB_succ' 4 84 87 (Eq.refl
  Bool.true) (allA_succ_of_gcd 3 84 87 3 1 28 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 2 84 87 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 84 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 87 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 84
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84 87)))) (allB_succ' 5 83 87 (Eq.refl
  Bool.true) (allA_succ_of_accept 4 83 87 (accept_3_4 4 83 87 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 83 87 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 83 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 87 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 83 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 87 (accept_3_4 1 83 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 83 87))))) (allB_succ' 6 82 87 (Eq.refl Bool.true) (allA_succ_of_accept 5 82
  87 (accept_3_5 5 82 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 82 87
  (Polychromatic418967fa.accept_9_4_1_6_1_284 4 82 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 82 87 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 82 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 87 (accept_3_5 2 82 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 82 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 82 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82 87)))))) (allB_succ' 7 81 87 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 81 87 3 2 27 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 81 87 (Polychromatic418967fa.accept_11_5_4_10_1_524 5 81 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 87 (Polychromatic418967fa.accept_10_4_1_7_1_371 4 81 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 81 87 3 1 27 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 81 87
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 81 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 81 87 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 81 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 81 87))))))) (allB_succ' 8 80 87 (Eq.refl Bool.true) (allA_succ_of_accept 7
  80 87 (accept_3_4 7 80 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80 87
  (Polychromatic418967fa.accept_12_6_8_3_1_82 6 80 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 80 87 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 80 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 80 87 (accept_3_4 4 80 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 80 87 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 80 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 87 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 80
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 80 87 (accept_3_4 1 80 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80 87)))))))) (allB_succ' 9 79 87 (Eq.refl Bool.true)
  (allA_succ_of_accept 8 79 87 (accept_3_5 8 79 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 87
  (Polychromatic418967fa.accept_15_7_4_12_1_2530 7 79 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 79 87 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 79 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 87 (accept_3_5 5 79 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 79 87 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 79 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 87 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 79
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 87 (accept_3_5 2 79 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79 87 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 79
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79 87))))))))) (allB_succ' 10 78 87 (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 78 87 3 3 26 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 78 87 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 78 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 87 (Polychromatic418967fa.accept_15_7_3_12_1_365 7
  78 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 87 3 2 26 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 87
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 78 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 78 87 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 78 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 78 87 3 1 26 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 78 87 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 78 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 78 87
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 78 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 78 87)))))))))) (allB_succ' 11 77 87 (Eq.refl Bool.true) (allA_succ_of_accept 10 77 87 (accept_3_4 10 77 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 77 87 (Polychromatic418967fa.accept_12_9_5_3_1_782 9
  77 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 77 87
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 77 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 77 87 (accept_3_4 7 77 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 87
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 77 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 77 87 (Polychromatic418967fa.accept_15_5_2_12_1_2543 5 77 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 77 87 (accept_3_4 4 77 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 77 87 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 77 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 77 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 77
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 87 (accept_3_4 1 77 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 77 87))))))))))) (allB_succ' 12 76 87 (Eq.refl Bool.true)
  (allA_succ_of_accept 11 76 87 (accept_3_5 11 76 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 76
  87 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 76 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 76 87 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 76 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 76 87 (accept_3_5 8 76 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 76 87 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 76 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 76 87 (Polychromatic418967fa.accept_12_6_4_3_1_361 6
  76 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 76 87 (accept_3_5 5 76 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 76 87 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 76
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 76 87
  (Polychromatic418967fa.accept_8_3_4_7_1_475 3 76 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 76 87 (accept_3_5 2 76 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 76 87
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 76 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 76 87)))))))))))) (allB_succ' 13 75 87 (Eq.refl Bool.true) (allA_succ_of_gcd 12 75 87 3 4 25 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 75 87
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 75 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 75 87 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 75 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 75 87 3 3 25 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 75 87 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 75 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 87
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 75 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 75 87 3 2 25 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 75 87 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 75 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 87 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 75 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 75 87 3 1 25 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 75 87
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 75 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 75 87 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 75 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 75 87))))))))))))) (allB_succ' 14 74 87 (Eq.refl Bool.true)
  (allA_succ_of_accept 13 74 87 (accept_3_4 13 74 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 74
  87 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 74 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 74 87 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 74 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 87 (accept_3_4 10 74 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 74 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 74 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 87 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 74
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 74 87 (accept_3_4 7 74 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74 87 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 74
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 74 87
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 74 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 74 87 (accept_3_4 4 74 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 74 87
  (Polychromatic418967fa.accept_9_3_2_6_1_264 3 74 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 74 87 (Polychromatic418967fa.accept_10_2_4_7_1_352 2 74 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 87 (accept_3_4 1 74 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 74 87)))))))))))))) (allB_succ' 15 73 87 (Eq.refl Bool.true) (allA_succ_of_accept 14 73 87
  (accept_3_5 14 73 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 87
  (Polychromatic418967fa.accept_9_4_1_6_1_284 13 73 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 73 87 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 73 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 73 87 (accept_3_5 11 73 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 73 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 73 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 73 87 (Polychromatic418967fa.accept_12_9_1_3_1_350 9
  73 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 87 (accept_3_5 8 73 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 87 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 73
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 87
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 73 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 87 (accept_3_5 5 73 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73 87
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 73 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 87 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 73 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 87 (accept_3_5 2 73 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 87 (Polychromatic418967fa.accept_13_1_8_9_1_1154 1 73 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73 87))))))))))))))) (allB_succ' 16 72 87 (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 72 87 3 5 24 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 72 87 (Polychromatic418967fa.accept_10_4_2_7_1_373 14 72 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 87 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 72 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 87 3 4 24 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 87
  (Polychromatic418967fa.accept_13_11_7_9_1_612 11 72 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 72 87 (Polychromatic418967fa.accept_19_10_15_11_1_3421 10 72 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 72 87 3 3 24 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 72 87 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 72 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 87
  (Polychromatic418967fa.accept_19_7_15_11_1_3420 7 72 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 72 87 3 2 24 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 72 87 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 72 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 72 87 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 72 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 72 87 3 1 24 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 72 87
  (Polychromatic418967fa.accept_13_2_7_9_1_2616 2 72 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 72 87 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 72 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 72 87)))))))))))))))) (allB_succ' 17 71 87 (Eq.refl Bool.true)
  (allA_succ_of_accept 16 71 87 (accept_3_4 16 71 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 71
  87 (Polychromatic418967fa.accept_11_4_5_10_1_926 15 71 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 71 87 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 71 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 87 (accept_3_4 13 71 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 71 87 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 71 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 87 (Polychromatic418967fa.accept_7_4_1_3_1_277 11
  71 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 71 87 (accept_3_4 10 71 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 71 87 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 71
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 87
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 71 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 71 87 (accept_3_4 7 71 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 87
  (Polychromatic418967fa.accept_10_6_1_7_1_342 6 71 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 71 87 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 71 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 71 87 (accept_3_4 4 71 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 71 87 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 71 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 87 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 71
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 87 (accept_3_4 1 71 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 71 87))))))))))))))))) (allB_succ' 18 70 87 (Eq.refl Bool.true)
  (allA_succ_of_accept 17 70 87 (accept_3_5 17 70 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 70
  87 (Polychromatic418967fa.accept_11_5_4_10_1_524 16 70 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 70 87 (Polychromatic418967fa.accept_13_2_5_9_1_610 15 70 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 70 87 (accept_3_5 14 70 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 70 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 70 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 70 87 (Polychromatic418967fa.accept_9_3_7_6_1_76 12
  70 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 70 87 (accept_3_5 11 70 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 70 87 (Polychromatic418967fa.accept_9_1_7_6_1_75 10
  70 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 70 87
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 70 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 70 87 (accept_3_5 8 70 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 70 87
  (Polychromatic418967fa.accept_6_1_4_3_1_14 7 70 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 70 87 (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 70 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 70 87 (accept_3_5 5 70 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 70 87 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 70 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 70 87 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 70
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 70 87 (accept_3_5 2 70 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 70 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 70
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70 87)))))))))))))))))) (allB_succ' 19 69 87
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 69 87 3 6 23 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 69 87 (Polychromatic418967fa.accept_12_5_9_3_1_85 17 69 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 87
  (Polychromatic418967fa.accept_7_2_6_3_1_100 16 69 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 69 87 3 5 23 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 69 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 69 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 87 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 69 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 69 87 3 4 23 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 69 87
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 69 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 69 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 69 87 3 3 23 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 69 87 (Polychromatic418967fa.accept_10_8_9_7_1_1118 8 69 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 87
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 7 69 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 69 87 3 2 23 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 69 87 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 69 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 87 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 69 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 69 87 3 1 23 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 87
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 69 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 69 87 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 69 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 69 87))))))))))))))))))) (allB_succ' 20 68 87 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 68 87 (accept_3_4 19 68 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 68
  87 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 68 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 68 87 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 68 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 87 (accept_3_4 16 68 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 68 87 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 68 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 87 (Polychromatic418967fa.accept_16_14_4_7_1_2380
  14 68 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 68 87 (accept_3_4 13 68
  87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 68 87 (Polychromatic418967fa.accept_9_3_5_6_1_253
  12 68 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 68 87
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 68 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 68 87 (accept_3_4 10 68 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 68
  87 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 68 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 68 87 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 68 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 68 87 (accept_3_4 7 68 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 68 87 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 68 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 68 87 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 68
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 87 (accept_3_4 4 68 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 68 87 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 68
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 87
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 68 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 68 87 (accept_3_4 1 68 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  87)))))))))))))))))))) (allB_succ' 21 67 87 (Eq.refl Bool.true) (allA_succ_of_accept 20 67 87 (accept_3_5 20 67 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 87 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 67
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 87
  (Polychromatic418967fa.accept_13_5_2_9_1_1195 18 67 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 87 (accept_3_5 17 67 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 67
  87 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 67 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 67 87 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 67 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 87 (accept_3_5 14 67 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 67 87 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 67 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 87 (Polychromatic418967fa.accept_8_4_3_7_1_491 12
  67 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 67 87 (accept_3_5 11 67 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 67 87 (Polychromatic418967fa.accept_6_4_1_3_1_77 10
  67 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 67 87
  (Polychromatic418967fa.accept_11_9_1_10_1_920 9 67 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 67 87 (accept_3_5 8 67 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 87
  (Polychromatic418967fa.accept_9_7_4_6_1_273 7 67 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 67 87 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 67 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 67 87 (accept_3_5 5 67 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 67 87 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 67 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 67 87 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 67
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 87 (accept_3_5 2 67 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 87 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 67
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67 87))))))))))))))))))))) (allB_succ' 22 66
  87 (Eq.refl Bool.true) (allA_succ_of_gcd 21 66 87 3 7 22 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 66 87 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 66 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 87
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 66 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 66 87 3 6 22 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 66 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 66 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 66 87 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 66 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 66 87 3 5 22 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 66 87
  (Polychromatic418967fa.accept_9_5_3_6_1_269 14 66 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 66 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 66 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 87 3 4 22 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 87 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 66 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 66 87
  (Polychromatic418967fa.accept_9_1_3_6_1_70 10 66 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 66 87 3 3 22 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 66 87 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 66 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 87 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 66 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 87 3 2 22 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 87
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 66 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 66 87 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 66 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 66 87 3 1 22 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 66 87 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 66 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 87
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 66 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 66 87)))))))))))))))))))))) (allB_succ' 23 65 87 (Eq.refl Bool.true) (allA_succ_of_accept 22 65 87
  (accept_3_4 22 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 65 87
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 65 87 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 65 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 87 (accept_3_4 19 65 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 65 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 65 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 87 (Polychromatic418967fa.accept_9_8_2_6_1_875 17
  65 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 87 (accept_3_4 16 65 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 65 87 (Polychromatic418967fa.accept_7_1_2_3_1_257 15
  65 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 65 87
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 65 87 (accept_3_4 13 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 65
  87 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 65 87 (Polychromatic418967fa.accept_25_11_15_12_1_3419 11 65 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 65 87 (accept_3_4 10 65 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 65 87 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 65 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 87 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 65
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 87 (accept_3_4 7 65 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 65
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 87
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 87 (accept_3_4 4 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65 87
  (Polychromatic418967fa.accept_9_3_2_6_1_264 3 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 65 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 87 (accept_3_4 1 65 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 87))))))))))))))))))))))) (allB_succ' 24 64 87 (Eq.refl Bool.true) (allA_succ_of_accept 23 64
  87 (accept_3_5 23 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 64 87
  (Polychromatic418967fa.accept_9_4_1_6_1_284 22 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 64 87 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 64 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 64 87 (accept_3_5 20 64 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 64 87 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 64 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 64 87 (Polychromatic418967fa.accept_7_4_1_3_1_277 18
  64 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 64 87 (accept_3_5 17 64 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 64 87 (Polychromatic418967fa.accept_7_2_1_3_1_102 16
  64 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 64 87
  (Polychromatic418967fa.accept_17_15_13_2_1_3418 15 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 64 87 (accept_3_5 14 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 64
  87 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 64 87 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 64 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 64 87 (accept_3_5 11 64 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 64 87 (Polychromatic418967fa.accept_13_10_12_9_1_1837 10 64 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 64 87 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 64
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 64 87 (accept_3_5 8 64 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 64 87 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 64
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 64 87
  (Polychromatic418967fa.accept_12_6_4_3_1_361 6 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 64 87 (accept_3_5 5 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 64 87
  (Polychromatic418967fa.accept_7_4_1_3_1_277 4 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 64 87 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 64 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 64 87 (accept_3_5 2 64 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 64 87 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 64 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64 87)))))))))))))))))))))))) (allB_succ' 25 63 87 (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 63 87 3 8 21 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 63 87 (Polychromatic418967fa.accept_15_8_3_12_1_1657 23 63 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 87 (Polychromatic418967fa.accept_15_7_3_12_1_365
  22 63 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63 87 3 7 21 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 63 87
  (Polychromatic418967fa.accept_11_9_8_10_1_934 20 63 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 87 (Polychromatic418967fa.accept_16_3_15_7_1_3417 19 63 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 63 87 3 6 21 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 63 87 (Polychromatic418967fa.accept_15_2_3_12_1_891 17 63 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 87
  (Polychromatic418967fa.accept_10_6_3_7_1_2197 16 63 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 63 87 3 5 21 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 63 87 (Polychromatic418967fa.accept_10_4_3_7_1_1110 14 63 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 87 (Polychromatic418967fa.accept_15_13_3_12_1_1609 13 63 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 63 87 3 4 21 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 63 87
  (Polychromatic418967fa.accept_14_11_7_3_1_3416 11 63 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 63 87 (Polychromatic418967fa.accept_14_10_7_3_1_1022 10 63 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 63 87 3 3 21 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 63 87 (Polychromatic418967fa.accept_13_8_11_9_1_593 8 63 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 87
  (Polychromatic418967fa.accept_13_7_11_9_1_1858 7 63 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 63 87 3 2 21 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 63 87 (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 63 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 87 (Polychromatic418967fa.accept_10_4_3_7_1_1110 4 63 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 63 87 3 1 21 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 63 87
  (Polychromatic418967fa.accept_13_2_11_9_1_591 2 63 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 63 87 (Polychromatic418967fa.accept_13_1_11_9_1_1857 1 63 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 63 87))))))))))))))))))))))))) (allB_succ' 26 62 87 (Eq.refl Bool.true)
  (allA_succ_of_accept 25 62 87 (accept_3_4 25 62 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 62
  87 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 62 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 62 87 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 62 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 62 87 (accept_3_4 22 62 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 62 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 62 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 62 87 (Polychromatic418967fa.accept_9_2_8_6_1_79 20
  62 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 62 87 (accept_3_4 19 62 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 62 87 (Polychromatic418967fa.accept_7_4_6_3_1_271 18
  62 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 62 87
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 62 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 62 87 (accept_3_4 16 62 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 62
  87 (Polychromatic418967fa.accept_10_5_2_7_1_345 15 62 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 62 87 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 62 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 62 87 (accept_3_4 13 62 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 62 87 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 62 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 62 87 (Polychromatic418967fa.accept_6_5_2_3_1_81 11
  62 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 62 87 (accept_3_4 10 62 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 62 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 62
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 62 87
  (Polychromatic418967fa.accept_17_8_11_2_1_3415 8 62 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 62 87 (accept_3_4 7 62 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 62 87
  (Polychromatic418967fa.accept_12_6_2_3_1_354 6 62 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 62 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 62 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 87 (accept_3_4 4 62 87 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 62 87 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 62 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 87 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 62 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 87 (accept_3_4 1 62 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 62 87)))))))))))))))))))))))))) (allB_succ' 27 61 87 (Eq.refl Bool.true)
  (allA_succ_of_accept 26 61 87 (accept_3_5 26 61 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 61
  87 (Polychromatic418967fa.accept_16_9_13_7_1_1509 25 61 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 61 87 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 61 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 61 87 (accept_3_5 23 61 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 61 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 61 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 61 87
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 61 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 61 87 (accept_3_5 20 61 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 61
  87 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 61 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 61 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 61 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 61 87 (accept_3_5 17 61 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 61 87 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 61 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 61 87 (Polychromatic418967fa.accept_7_1_5_3_1_268 15
  61 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 87 (accept_3_5 14 61 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 87 (Polychromatic418967fa.accept_9_4_7_6_1_255 13
  61 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 87
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 61 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 87 (accept_3_5 11 61 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 61
  87 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 61 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 61 87 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 61 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 87 (accept_3_5 8 61 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 61 87 (Polychromatic418967fa.accept_19_7_4_11_1_3414 7 61 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 61
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 61 87 (accept_3_5 5 61 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61 87 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 61
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 61 87
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 61 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 61 87 (accept_3_5 2 61 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 61 87
  (Polychromatic418967fa.accept_7_1_5_3_1_268 1 61 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 61 87))))))))))))))))))))))))))) (allB_succ' 28 60 87 (Eq.refl Bool.true) (allA_succ_of_gcd 27 60 87 3 9 20
  29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 60 87
  (Polychromatic418967fa.accept_11_4_5_10_1_926 26 60 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 60 87 (Polychromatic418967fa.accept_13_12_8_9_1_1833 25 60 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 87 3 8 20 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 87 (Polychromatic418967fa.accept_18_5_6_15_1_3413 23 60 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 60 87
  (Polychromatic418967fa.accept_7_1_4_3_1_21 22 60 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 60 87 3 7 20 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 60 87 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 60 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 87 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 60 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 87 3 6 20 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 87
  (Polychromatic418967fa.accept_11_6_5_10_1_2724 17 60 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 60 87 (Polychromatic418967fa.accept_13_3_8_9_1_1134 16 60 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 60 87 3 5 20 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 60 87 (Polychromatic418967fa.accept_13_1_8_9_1_1154 14 60 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 87
  (Polychromatic418967fa.accept_7_6_4_3_1_266 13 60 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 60 87 3 4 20 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 60 87 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 60 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 60 87 (Polychromatic418967fa.accept_18_10_6_15_1_3412 10 60 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 60 87 3 3 20 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 60 87
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 60 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 60 87 (Polychromatic418967fa.accept_13_7_8_9_1_1158 7 60 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 87 3 2 20 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 87 (Polychromatic418967fa.accept_16_5_12_7_1_3411 5 60 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 60 87
  (Polychromatic418967fa.accept_11_4_5_10_1_926 4 60 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 60 87 3 1 20 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 60 87 (Polychromatic418967fa.accept_16_2_12_7_1_3410 2 60 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 87 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 60 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60 87)))))))))))))))))))))))))))) (allB_succ'
  29 59 87 (Eq.refl Bool.true) (allA_succ_of_accept 28 59 87 (accept_3_4 28 59 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 59 87 (Polychromatic418967fa.accept_11_5_4_10_1_524 27 59 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 59 87 (Polychromatic418967fa.accept_6_2_5_3_1_16 26
  59 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 87 (accept_3_4 25 59 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 87 (Polychromatic418967fa.accept_13_11_7_9_1_612
  24 59 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 87
  (Polychromatic418967fa.accept_19_4_2_11_1_3409 23 59 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 87 (accept_3_4 22 59 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 59
  87 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 59 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 59 87 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 59 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 87 (accept_3_4 19 59 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 59 87 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 59 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 87 (Polychromatic418967fa.accept_9_8_5_6_1_538 17
  59 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 59 87 (accept_3_4 16 59 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 59 87 (Polychromatic418967fa.accept_13_2_7_9_1_2616
  15 59 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 59 87
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 59 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 59 87 (accept_3_4 13 59 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 59
  87 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 59 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 59 87 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 59 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 59 87 (accept_3_4 10 59 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 59 87 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 59 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 59 87 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 59
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 87 (accept_3_4 7 59 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 87 (Polychromatic418967fa.accept_13_6_7_9_1_1848 6
  59 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 87
  (Polychromatic418967fa.accept_11_5_4_10_1_524 5 59 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 87 (accept_3_4 4 59 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59 87
  (Polychromatic418967fa.accept_9_3_5_6_1_253 3 59 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 87 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 59 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 87 (accept_3_4 1 59 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 87))))))))))))))))))))))))))))) (allB_succ' 30 58 87 (Eq.refl Bool.true) (allA_succ_of_gcd 29
  58 87 29 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 28
  58 87 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 58 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 58 87 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 58 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 58 87 (accept_3_5 26 58 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 58 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 58 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 58 87 (Polychromatic418967fa.accept_18_6_4_15_1_2276
  24 58 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 58 87 (accept_3_5 23 58
  87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 58 87 (Polychromatic418967fa.accept_7_1_2_3_1_257
  22 58 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 58 87
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 58 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 58 87 (accept_3_5 20 58 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 58
  87 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 58 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 58 87 (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 58 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 58 87 (accept_3_5 17 58 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 58 87 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 58 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 58 87 (Polychromatic418967fa.accept_7_1_2_3_1_257 15
  58 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 58 87 (accept_3_5 14 58 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 58 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 58
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 58 87
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 58 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 58 87 (accept_3_5 11 58 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 58
  87 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 58 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 58 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 58 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 8 58 87 (accept_3_5 8 58 87 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 58 87 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 58 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 58 87 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 58 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 58 87 (accept_3_5 5 58 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 58 87 (Polychromatic418967fa.accept_13_4_6_9_1_3401 4 58 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 58 87
  (Polychromatic418967fa.accept_9_3_4_6_1_252 3 58 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 58 87 (accept_3_5 2 58 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 58 87
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 58 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 58 87)))))))))))))))))))))))))))))) (allB_succ' 31 57 87 (Eq.refl Bool.true) (allA_succ_of_gcd 30 57 87 3 10
  19 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 57 87
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 57 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 57 87 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 57 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 57 87 3 9 19 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 57 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 57 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 87
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 57 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 57 87 3 8 19 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 57 87 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 57 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 57 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 57 87 3 7 19 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 57 87
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 57 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 87 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 57 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 57 87 3 6 19 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 57 87 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 57 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 87
  (Polychromatic418967fa.accept_7_2_1_3_1_102 16 57 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 57 87 3 5 19 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 57 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 57 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 87 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 57 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 57 87 3 4 19 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 57 87
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 57 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 57 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 57 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 57 87 3 3 19 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 57 87 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 57 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 87
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 57 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 57 87 3 2 19 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 57 87 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 57 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 87 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 57 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 57 87 3 1 19 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 57 87
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 57 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 57 87 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 57 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 57 87))))))))))))))))))))))))))))))) (allB_succ' 32 56 87 (Eq.refl
  Bool.true) (allA_succ_of_accept 31 56 87 (accept_3_4 31 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 56 87 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 56 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 56 87 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 56 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 87 (accept_3_4 28 56 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 56 87 (Polychromatic418967fa.accept_19_8_18_11_1_3408
  27 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 87
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 56 87 (accept_3_4 25 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 56
  87 (Polychromatic418967fa.accept_11_2_1_10_1_196 24 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 56 87 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 56 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 87 (accept_3_4 22 56 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 56 87 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 56 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 87 (Polychromatic418967fa.accept_11_9_1_10_1_920
  20 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 56 87 (accept_3_4 19 56
  87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 56 87 (Polychromatic418967fa.accept_12_6_8_3_1_82
  18 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 56 87
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 56 87 (accept_3_4 16 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 56
  87 (Polychromatic418967fa.accept_16_15_8_7_1_3407 15 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 56 87 (Polychromatic418967fa.accept_9_5_2_6_1_265 14 56 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 56 87 (accept_3_4 13 56 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 56 87 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 56 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 56 87
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 56 87 (accept_3_4 10 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 56
  87 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 56 87 (Polychromatic418967fa.accept_9_8_2_6_1_875 8 56 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 56 87 (accept_3_4 7 56 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 56 87 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 56 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 56 87 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 56
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 87 (accept_3_4 4 56 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 56 87 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 56
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 87
  (Polychromatic418967fa.accept_11_2_1_10_1_196 2 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 56 87 (accept_3_4 1 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56
  87)))))))))))))))))))))))))))))))) (allB_succ' 33 55 87 (Eq.refl Bool.true) (allA_succ_of_accept 32 55 87 (accept_3_5
  32 55 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 87
  (Polychromatic418967fa.accept_9_4_1_6_1_284 31 55 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 55 87 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 55 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 55 87 (accept_3_5 29 55 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 55 87 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 55 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 87 (Polychromatic418967fa.accept_19_8_17_11_1_3406
  27 55 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 87 (accept_3_5 26 55
  87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 87 (Polychromatic418967fa.accept_7_4_6_3_1_271
  25 55 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 87
  (Polychromatic418967fa.accept_14_10_13_3_1_2552 24 55 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 55 87 (accept_3_5 23 55 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 55
  87 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 55 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 55 87 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 55 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 87 (accept_3_5 20 55 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 55 87 (Polychromatic418967fa.accept_13_6_3_9_1_1827 19 55 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 87 (Polychromatic418967fa.accept_7_4_6_3_1_271 18
  55 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 87 (accept_3_5 17 55 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 87 (Polychromatic418967fa.accept_6_4_1_3_1_77 16
  55 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 55 87
  (Polychromatic418967fa.accept_13_2_3_9_1_2610 15 55 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 55 87 (accept_3_5 14 55 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 55
  87 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 55 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 55 87 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 55 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 87 (accept_3_5 11 55 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 55 87 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 55 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 87 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 55
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 87 (accept_3_5 8 55 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 87 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 55
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 87
  (Polychromatic418967fa.accept_13_6_3_9_1_1827 6 55 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 87 (accept_3_5 5 55 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55 87
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 55 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 87 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 55 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 87 (accept_3_5 2 55 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 87 (Polychromatic418967fa.accept_20_1_15_7_1_3405 1 55 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 87))))))))))))))))))))))))))))))))) (allB_succ' 34 54 87
  (Eq.refl Bool.true) (allA_succ_of_gcd 33 54 87 3 11 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 54 87 (Polychromatic418967fa.accept_10_2_4_7_1_352 32 54 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 87
  (Polychromatic418967fa.accept_10_1_4_7_1_374 31 54 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 54 87 3 10 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 54 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 54 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 87 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 54 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 54 87 3 9 18 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 54 87
  (Polychromatic418967fa.accept_12_2_6_3_1_331 26 54 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 54 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 54 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 87 3 8 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 87 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 54 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 87
  (Polychromatic418967fa.accept_7_1_5_3_1_268 22 54 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 54 87 3 7 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 54 87 (Polychromatic418967fa.accept_12_8_6_3_1_366 20 54 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 87 (Polychromatic418967fa.accept_13_6_2_9_1_1188 19 54 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 87 3 6 18 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 87
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 54 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 54 87 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 54 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 54 87 3 5 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 54 87 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 54 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 87
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 54 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 54 87 3 4 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 54 87 (Polychromatic418967fa.accept_10_1_4_7_1_374 11 54 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 87 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 54 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 54 87 3 3 18 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 54 87
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 54 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 54 87 (Polychromatic418967fa.accept_13_7_2_9_1_1826 7 54 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 87 3 2 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 54 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 87
  (Polychromatic418967fa.accept_12_4_6_3_1_332 4 54 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 54 87 3 1 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 54 87 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 54 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 54 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54 87))))))))))))))))))))))))))))))))))
  (allB_succ' 35 53 87 (Eq.refl Bool.true) (allA_succ_of_accept 34 53 87 (accept_3_4 34 53 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 53 87 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 53 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 53 87
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 53 87 (accept_3_4 31 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 53
  87 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 53 87 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 53 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 87 (accept_3_4 28 53 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 53 87 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 53 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 53 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 26
  53 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 87 (accept_3_4 25 53 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 87 (Polychromatic418967fa.accept_10_4_3_7_1_1110
  24 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 87
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 87 (accept_3_4 22 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 53
  87 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 53 87 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 53 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 87 (accept_3_4 19 53 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 53 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 53 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 87 (Polychromatic418967fa.accept_25_17_3_12_1_3404
  17 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 87 (accept_3_4 16 53
  87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 53 87 (Polychromatic418967fa.accept_7_1_4_3_1_21
  15 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 87
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 53 87 (accept_3_4 13 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 53
  87 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 53 87 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 53 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 87 (accept_3_4 10 53 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 53 87 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 53 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 87 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 53
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 87 (accept_3_4 7 53 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 53
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 87
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 87 (accept_3_4 4 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53 87
  (Polychromatic418967fa.accept_9_3_8_6_1_80 3 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 53 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 87 (accept_3_4 1 53 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 87))))))))))))))))))))))))))))))))))) (allB_succ' 36 52 87 (Eq.refl Bool.true)
  (allA_succ_of_accept 35 52 87 (accept_3_5 35 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 52
  87 (Polychromatic418967fa.accept_10_4_2_7_1_373 34 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 52 87 (Polychromatic418967fa.accept_15_3_7_12_1_372 33 52 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 52 87 (accept_3_5 32 52 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 52 87 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 52 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 52 87 (Polychromatic418967fa.accept_9_3_7_6_1_76 30
  52 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 52 87 (accept_3_5 29 52 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 52 87 (Polychromatic418967fa.accept_9_1_7_6_1_75 28
  52 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 52 87
  (Polychromatic418967fa.accept_8_3_4_7_1_475 27 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 52 87 (accept_3_5 26 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 52
  87 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 52 87 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 52 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 52 87 (accept_3_5 23 52 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 52 87 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 52 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 52 87 (Polychromatic418967fa.accept_9_3_7_6_1_76 21
  52 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 52 87 (accept_3_5 20 52 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 52 87 (Polychromatic418967fa.accept_6_1_4_3_1_14 19
  52 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 52 87
  (Polychromatic418967fa.accept_12_6_4_3_1_361 18 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 52 87 (accept_3_5 17 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 52
  87 (Polychromatic418967fa.accept_17_16_1_2_1_3403 16 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 52 87 (Polychromatic418967fa.accept_10_5_2_7_1_345 15 52 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 52 87 (accept_3_5 14 52 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 52 87 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 52 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 52 87
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 52 87 (accept_3_5 11 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 52
  87 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 52 87 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 52 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 87 (accept_3_5 8 52 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 52 87 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 52 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 87 (Polychromatic418967fa.accept_12_6_4_3_1_361 6
  52 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 52 87 (accept_3_5 5 52 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52 87 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 52
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 52 87
  (Polychromatic418967fa.accept_8_3_4_7_1_475 3 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 52 87 (accept_3_5 2 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 52 87
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 52 87)))))))))))))))))))))))))))))))))))) (allB_succ' 37 51 87 (Eq.refl Bool.true) (allA_succ_of_gcd 36 51
  87 3 12 17 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  51 87 (Polychromatic418967fa.accept_15_5_6_12_1_916 35 51 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 51 87 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 51 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 51 87 3 11 17 29 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 51 87 (Polychromatic418967fa.accept_15_2_6_12_1_1613
  32 51 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 87
  (Polychromatic418967fa.accept_16_15_3_7_1_3389 31 51 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 51 87 3 10 17 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 51 87 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 51 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 87 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 51 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 51 87 3 9 17 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 51 87
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 51 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 87 (Polychromatic418967fa.accept_11_3_7_10_1_180 25 51 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 51 87 3 8 17 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 51 87 (Polychromatic418967fa.accept_13_10_12_9_1_1837 23 51 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 87
  (Polychromatic418967fa.accept_7_1_2_3_1_257 22 51 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 51 87 3 7 17 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 51 87 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 51 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 87 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 51 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 51 87 3 6 17 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 51 87
  (Polychromatic418967fa.accept_15_2_6_12_1_1613 17 51 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 51 87 (Polychromatic418967fa.accept_10_6_1_7_1_342 16 51 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 51 87 3 5 17 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 51 87 (Polychromatic418967fa.accept_10_4_1_7_1_371 14 51 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 87
  (Polychromatic418967fa.accept_7_6_2_3_1_107 13 51 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 51 87 3 4 17 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 51 87 (Polychromatic418967fa.accept_16_11_3_7_1_2375 11 51 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 87 (Polychromatic418967fa.accept_13_10_12_9_1_1837 10 51 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 51 87 3 3 17 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 51 87
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 51 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 87 (Polychromatic418967fa.accept_15_7_6_12_1_1614 7 51 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 51 87 3 2 17 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 51 87 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 51 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 87
  (Polychromatic418967fa.accept_8_4_3_7_1_491 4 51 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 51 87 3 1 17 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 51 87 (Polychromatic418967fa.accept_15_2_6_12_1_1613 2 51 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 87 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 51 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 87)))))))))))))))))))))))))))))))))))))
  (allB_succ' 38 50 87 (Eq.refl Bool.true) (allA_succ_of_accept 37 50 87 (accept_3_4 37 50 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 50 87 (Polychromatic418967fa.accept_15_6_5_12_1_1642 36 50 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 50 87
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 50 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 50 87 (accept_3_4 34 50 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 50
  87 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 50 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 50 87 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 50 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 50 87 (accept_3_4 31 50 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 50 87 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 50 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 50 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 50
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 87 (accept_3_4 28 50 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 87 (Polychromatic418967fa.accept_11_5_6_10_1_1432
  27 50 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 87
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 50 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 50 87 (accept_3_4 25 50 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 50
  87 (Polychromatic418967fa.accept_15_9_5_12_1_1640 24 50 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 50 87 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 50 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 87 (accept_3_4 22 50 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 50 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 87
  (Polychromatic418967fa.accept_9_2_5_6_1_536 20 50 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 50 87 (accept_3_4 19 50 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 50
  87 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 50 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 50 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 50 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 87 (accept_3_4 16 50 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 50 87 (Polychromatic418967fa.accept_13_2_11_9_1_591 15 50 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 87 (Polychromatic418967fa.accept_13_1_11_9_1_1857
  14 50 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 50 87 (accept_3_4 13 50
  87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 50 87 (Polychromatic418967fa.accept_7_5_1_3_1_103
  12 50 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 50 87
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 50 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 50 87 (accept_3_4 10 50 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 50
  87 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 50 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 50 87 (Polychromatic418967fa.accept_9_8_5_6_1_538 8 50 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 50 87 (accept_3_4 7 50 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 50 87 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 50 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 50 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 50
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 50 87 (accept_3_4 4 50 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 50 87 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 50
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 87
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 50 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 50 87 (accept_3_4 1 50 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50
  87)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 49 87 (Eq.refl Bool.true) (allA_succ_of_accept 38 49 87
  (accept_3_5 38 49 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 87
  (Polychromatic418967fa.accept_9_1_4_6_1_5 37 49 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 49 87 (Polychromatic418967fa.accept_20_16_9_7_1_3402 36 49 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 87 (accept_3_5 35 49 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 49 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 49 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 87 (Polychromatic418967fa.accept_12_9_1_3_1_350 33
  49 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 87 (accept_3_5 32 49 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 87 (Polychromatic418967fa.accept_15_1_4_12_1_2401
  31 49 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 87
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 49 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 87 (accept_3_5 29 49 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 49
  87 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 49 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 49 87 (Polychromatic418967fa.accept_13_1_10_9_1_215 27 49 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 87 (accept_3_5 26 49 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 49 87 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 49 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 87 (Polychromatic418967fa.accept_14_10_7_3_1_1022
  24 49 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 87 (accept_3_5 23 49
  87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 87 (Polychromatic418967fa.accept_4_2_1_3_1_27
  22 49 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 87
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 49 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 87 (accept_3_5 20 49 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 49
  87 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 49 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 49 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 49 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 87 (accept_3_5 17 49 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 49 87 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 49 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 87 (Polychromatic418967fa.accept_11_4_5_10_1_926
  15 49 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 87 (accept_3_5 14 49
  87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 87
  (Polychromatic418967fa.accept_17_13_15_2_1_654 13 49 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 49 87 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 49 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 87 (accept_3_5 11 49 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 49 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 49 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 87 (Polychromatic418967fa.accept_12_9_1_3_1_350 9
  49 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 87 (accept_3_5 8 49 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 87 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 49
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 87
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 49 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 87 (accept_3_5 5 49 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49 87
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 49 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 49 87 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 49 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 87 (accept_3_5 2 49 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 49 87 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 49 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 87))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 48 87
  (Eq.refl Bool.true) (allA_succ_of_gcd 39 48 87 3 13 16 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 38 48 87 (Polychromatic418967fa.accept_9_2_3_6_1_88 38 48 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 87
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 48 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 48 87 3 12 16 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 48 87 (Polychromatic418967fa.accept_9_8_3_6_1_533 35 48 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 48 87 (Polychromatic418967fa.accept_9_7_3_6_1_270 34 48 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 48 87 3 11 16 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 48 87
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 48 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 48 87 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 48 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 87 3 10 16 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 87 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 48 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 48 87
  (Polychromatic418967fa.accept_9_1_3_6_1_70 28 48 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 48 87 3 9 16 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 48 87 (Polychromatic418967fa.accept_9_8_3_6_1_533 26 48 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 87 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 48 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 87 3 8 16 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 87
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 48 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 48 87 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 48 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 48 87 3 7 16 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 48 87 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 48 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 87
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 48 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 48 87 3 6 16 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 48 87 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 48 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 48 87 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 48 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 48 87 3 5 16 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 48 87
  (Polychromatic418967fa.accept_9_5_3_6_1_269 14 48 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 48 87 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 48 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 87 3 4 16 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 87 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 48 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 48 87
  (Polychromatic418967fa.accept_9_1_3_6_1_70 10 48 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 48 87 3 3 16 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 48 87 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 48 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 87 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 48 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 87 3 2 16 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 87
  (Polychromatic418967fa.accept_9_5_3_6_1_269 5 48 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 48 87 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 48 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 48 87 3 1 16 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 48 87 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 48 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 87
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 48 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 48 87)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 47 87 (Eq.refl Bool.true) (allA_succ_of_accept
  40 47 87 (accept_3_4 40 47 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 87
  (Polychromatic418967fa.accept_9_3_2_6_1_264 39 47 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 47 87 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 47 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 87 (accept_3_4 37 47 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 47 87 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 47 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 87 (Polychromatic418967fa.accept_9_8_2_6_1_875 35
  47 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 87 (accept_3_4 34 47 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 87 (Polychromatic418967fa.accept_12_9_11_3_1_772
  33 47 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 47 87
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 47 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 47 87 (accept_3_4 31 47 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 47
  87 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 47 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 47 87 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 47 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 87 (accept_3_4 28 47 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 47 87 (Polychromatic418967fa.accept_13_1_8_9_1_1154 27 47 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 47 87 (Polychromatic418967fa.accept_6_2_5_3_1_16 26
  47 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 87 (accept_3_4 25 47 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 87 (Polychromatic418967fa.accept_13_11_8_9_1_1161
  24 47 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 87
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 47 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 87 (accept_3_4 22 47 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 47
  87 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 47 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 47 87 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 47 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 87 (accept_3_4 19 47 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 47 87 (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 47 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 87 (Polychromatic418967fa.accept_9_8_2_6_1_875 17
  47 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 87 (accept_3_4 16 47 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 87 (Polychromatic418967fa.accept_7_1_5_3_1_268 15
  47 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 87
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 47 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 47 87 (accept_3_4 13 47 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 47
  87 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 47 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 47 87 (Polychromatic418967fa.accept_13_11_8_9_1_1161 11 47 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 87 (accept_3_4 10 47 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 47 87 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 47 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 87 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 47
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 87 (accept_3_4 7 47 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 87 (Polychromatic418967fa.accept_15_6_2_12_1_885 6
  47 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 87
  (Polychromatic418967fa.accept_9_5_2_6_1_265 5 47 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 87 (accept_3_4 4 47 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47 87
  (Polychromatic418967fa.accept_9_3_2_6_1_264 3 47 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 87 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 47 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 87 (accept_3_4 1 47 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 87))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 46 87 (Eq.refl Bool.true)
  (allA_succ_of_accept 41 46 87 (accept_3_5 41 46 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 46
  87 (Polychromatic418967fa.accept_9_4_1_6_1_284 40 46 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 46 87 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 46 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 46 87 (accept_3_5 38 46 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 46 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 46 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 46 87 (Polychromatic418967fa.accept_7_1_4_3_1_21 36
  46 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 87 (accept_3_5 35 46 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 87 (Polychromatic418967fa.accept_7_6_4_3_1_266 34
  46 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 46 87
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 46 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 46 87 (accept_3_5 32 46 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 46
  87 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 46 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 46 87 (Polychromatic418967fa.accept_9_3_1_6_1_86 30 46 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 87 (accept_3_5 29 46 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 46 87 (Polychromatic418967fa.accept_13_2_7_9_1_2616 28 46 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 46 87 (Polychromatic418967fa.accept_7_6_4_3_1_266 27
  46 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 46 87 (accept_3_5 26 46 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 46 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 46
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 46 87
  (Polychromatic418967fa.accept_13_11_7_9_1_612 24 46 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 46 87 (accept_3_5 23 46 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 46
  87 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 46 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 46 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 46 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 46 87 (accept_3_5 20 46 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 46 87 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 46 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 46 87 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  18 46 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 87 (accept_3_5 17 46
  87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 87 (Polychromatic418967fa.accept_9_7_1_6_1_261
  16 46 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 87
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 46 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 46 87 (accept_3_5 14 46 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 46
  87 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 46 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 46 87 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 46 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 87 (accept_3_5 11 46 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 46 87 (Polychromatic418967fa.accept_16_10_14_7_1_2372 10 46 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 46 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 46
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 46 87 (accept_3_5 8 46 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 46 87 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 46
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 46 87
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 46 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 46 87 (accept_3_5 5 46 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 46 87
  (Polychromatic418967fa.accept_9_4_1_6_1_284 4 46 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 46 87 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 46 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 87 (accept_3_5 2 46 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 46 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 46 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46 87)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 45
  87 (Eq.refl Bool.true) (allA_succ_of_gcd 42 45 87 3 14 15 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 45 87 (Polychromatic418967fa.accept_12_5_9_3_1_85 41 45 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 87
  (Polychromatic418967fa.accept_13_1_6_9_1_1197 40 45 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 45 87 3 13 15 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 45 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 45 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 87 (Polychromatic418967fa.accept_12_1_9_3_1_370 37 45 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 45 87 3 12 15 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 45 87
  (Polychromatic418967fa.accept_11_2_1_10_1_196 35 45 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 45 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 45 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 45 87 3 11 15 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 45 87 (Polychromatic418967fa.accept_10_2_5_7_1_1124 32 45 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 87
  (Polychromatic418967fa.accept_11_9_1_10_1_920 31 45 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 45 87 3 10 15 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 45 87 (Polychromatic418967fa.accept_12_5_9_3_1_85 29 45 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 87 (Polychromatic418967fa.accept_10_8_5_7_1_358 28 45 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 45 87 3 9 15 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 45 87
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 45 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 87 (Polychromatic418967fa.accept_12_1_9_3_1_370 25 45 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 45 87 3 8 15 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 87 (Polychromatic418967fa.accept_10_3_5_7_1_330 23 45 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 87
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 45 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 45 87 3 7 15 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 45 87 (Polychromatic418967fa.accept_11_9_1_10_1_920 20 45 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 87 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 45 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 45 87 3 6 15 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 45 87
  (Polychromatic418967fa.accept_12_5_9_3_1_85 17 45 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 45 87 (Polychromatic418967fa.accept_13_3_6_9_1_1150 16 45 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 87 3 5 15 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 45 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 87
  (Polychromatic418967fa.accept_10_3_5_7_1_330 13 45 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 45 87 3 4 15 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 45 87 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 45 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 45 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 45 87 3 3 15 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 45 87
  (Polychromatic418967fa.accept_10_8_5_7_1_358 8 45 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 87 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 45 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 87 3 2 15 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 45 87 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 45 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 87
  (Polychromatic418967fa.accept_13_4_6_9_1_3401 4 45 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 45 87 3 1 15 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 45 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 45 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 87 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 45 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  87))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 87 (allA_succ_of_accept 43 44 87 (accept_3_4 43 44 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 44 87 (Polychromatic418967fa.accept_10_2_4_7_1_352 42
  44 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 44 87
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 44 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 44 87 (accept_3_4 40 44 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 44
  87 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 44 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 44 87 (Polychromatic418967fa.accept_9_2_8_6_1_79 38 44 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 44 87 (accept_3_4 37 44 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 44 87 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 44 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 44 87 (Polychromatic418967fa.accept_6_5_2_3_1_81 35
  44 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 87 (accept_3_4 34 44 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 44 87 (Polychromatic418967fa.accept_7_5_2_3_1_106 33
  44 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 87
  (Polychromatic418967fa.accept_9_5_8_6_1_281 32 44 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 44 87 (accept_3_4 31 44 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 44
  87 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 44 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 44 87 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 44 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 87 (accept_3_4 28 44 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 44 87 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 44 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 87 (Polychromatic418967fa.accept_7_5_2_3_1_106 26
  44 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 44 87 (accept_3_4 25 44 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 44 87 (Polychromatic418967fa.accept_15_9_14_12_1_913
  24 44 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 44 87
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 44 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 44 87 (accept_3_4 22 44 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 44
  87 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 44 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 44 87 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 44 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 44 87 (accept_3_4 19 44 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 44 87 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 44 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 44 87 (Polychromatic418967fa.accept_6_5_2_3_1_81 17
  44 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 87 (accept_3_4 16 44 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 44 87 (Polychromatic418967fa.accept_7_1_2_3_1_257 15
  44 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 87
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 44 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 44 87 (accept_3_4 13 44 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 44
  87 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 44 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 44 87 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 44 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 87 (accept_3_4 10 44 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 44 87 (Polychromatic418967fa.accept_15_9_14_12_1_913 9 44 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 87 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 44
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 44 87 (accept_3_4 7 44 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44 87 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 44
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 44 87
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 44 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 44 87 (accept_3_4 4 44 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 44 87
  (Polychromatic418967fa.accept_8_3_4_7_1_475 3 44 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 44 87 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 44 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 87 (accept_3_4 1 44 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 44 87)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 87 (allA_succ_of_accept 42 43 87
  (Polychromatic418967fa.accept_28_14_15_3_1_3400 42 43 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 87 (accept_3_5 41 43 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 43
  87 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 43 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 43 87 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 43 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 87 (accept_3_5 38 43 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 43 87 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 43 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 87 (Polychromatic418967fa.accept_8_4_3_7_1_491 36
  43 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 43 87 (accept_3_5 35 43 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 43 87 (Polychromatic418967fa.accept_6_4_1_3_1_77 34
  43 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 43 87
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 43 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 43 87 (accept_3_5 32 43 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 43
  87 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 43 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 43 87 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 43 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 87 (accept_3_5 29 43 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 43 87 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 43 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 87 (Polychromatic418967fa.accept_21_6_1_3_1_3399
  27 43 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 87 (accept_3_5 26 43
  87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 87 (Polychromatic418967fa.accept_7_4_1_3_1_277
  25 43 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 87
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 43 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 87 (accept_3_5 23 43 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 43
  87 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 43 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 43 87 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 43 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 87 (accept_3_5 20 43 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 43 87 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 43 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 87 (Polychromatic418967fa.accept_7_4_1_3_1_277 18
  43 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 43 87 (accept_3_5 17 43 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 43 87 (Polychromatic418967fa.accept_6_4_1_3_1_77 16
  43 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 43 87
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 43 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 43 87 (accept_3_5 14 43 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 43
  87 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 43 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 43 87 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 43 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 87 (accept_3_5 11 43 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 43 87 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 43 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 87 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 43
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 87 (accept_3_5 8 43 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 87 (Polychromatic418967fa.accept_13_7_4_9_1_1865 7
  43 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 87
  (Polychromatic418967fa.accept_10_6_3_7_1_2197 6 43 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 87 (accept_3_5 5 43 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43 87
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 43 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 87 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 43 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 87 (accept_3_5 2 43 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 87 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 43 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 87))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 87
  (allA_succ_of_accept 41 42 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 42 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 42 87 (Polychromatic418967fa.accept_12_4_6_3_1_332 40 42 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 42 87 3 13 14 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 42 87
  (Polychromatic418967fa.accept_12_2_6_3_1_331 38 42 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 42 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 42 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 87 3 12 14 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 87 (Polychromatic418967fa.accept_10_5_2_7_1_345 35 42 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 42 87
  (Polychromatic418967fa.accept_10_4_2_7_1_373 34 42 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 42 87 3 11 14 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 42 87 (Polychromatic418967fa.accept_12_8_6_3_1_366 32 42 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 87 (Polychromatic418967fa.accept_13_5_3_9_1_1189 31 42 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 87 3 10 14 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 87
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 42 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 42 87 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 42 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 42 87 3 9 14 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 42 87 (Polychromatic418967fa.accept_12_2_6_3_1_331 26 42 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 87
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 42 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 87 3 8 14 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 42 87 (Polychromatic418967fa.accept_11_1_9_10_1_184 23 42 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 42 87 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 42 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 42 87 3 7 14 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 42 87
  (Polychromatic418967fa.accept_12_8_6_3_1_366 20 42 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 42 87 (Polychromatic418967fa.accept_10_9_2_7_1_1096 19 42 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 87 3 6 14 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 42 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 42 87
  (Polychromatic418967fa.accept_12_4_6_3_1_332 16 42 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 42 87 3 5 14 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 42 87 (Polychromatic418967fa.accept_10_4_2_7_1_373 14 42 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 42 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 87 3 4 14 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 87
  (Polychromatic418967fa.accept_17_11_8_2_1_3398 11 42 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 42 87 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 42 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 42 87 3 3 14 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 42 87 (Polychromatic418967fa.accept_11_8_9_10_1_503 8 42 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 87
  (Polychromatic418967fa.accept_13_7_3_9_1_1142 7 42 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 42 87 3 2 14 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 42 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 42 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 42 87 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 42 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 42 87 3 1 14 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 42 87
  (Polychromatic418967fa.accept_12_2_6_3_1_331 2 42 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 42 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 42 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 42 87)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 87 (allA_succ_of_accept
  40 41 87 (accept_3_4 40 41 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 87
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 41 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 41 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 87 (accept_3_4 37 41 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 87 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 41 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 87 (Polychromatic418967fa.accept_9_8_5_6_1_538 35
  41 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 87 (accept_3_4 34 41 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 87 (Polychromatic418967fa.accept_12_9_5_3_1_782 33
  41 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 87
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 41 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 87 (accept_3_4 31 41 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 41
  87 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 41 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 41 87 (Polychromatic418967fa.accept_9_2_5_6_1_536 29 41 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 87 (accept_3_4 28 41 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 41 87 (Polychromatic418967fa.accept_13_1_2_9_1_1186 27 41 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 26
  41 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 87 (accept_3_4 25 41 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 87 (Polychromatic418967fa.accept_10_4_1_7_1_371 24
  41 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 87
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 41 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 87 (accept_3_4 22 41 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 41
  87 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 41 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 41 87 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 41 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 87 (accept_3_4 19 41 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 41 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 41 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 87 (Polychromatic418967fa.accept_9_8_5_6_1_538 17
  41 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 87 (accept_3_4 16 41 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 87 (Polychromatic418967fa.accept_17_15_7_2_1_2303
  15 41 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 87
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 41 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 87 (accept_3_4 13 41 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 41
  87 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 41 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 41 87 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 41 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 87 (accept_3_4 10 41 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 41 87 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 41 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 87 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 41
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 87 (accept_3_4 7 41 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 41
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 87
  (Polychromatic418967fa.accept_13_5_2_9_1_1195 5 41 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 87 (accept_3_4 4 41 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41 87
  (Polychromatic418967fa.accept_9_3_5_6_1_253 3 41 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 41 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 87 (accept_3_4 1 41 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 87))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 87 (allA_succ_of_accept 39 40 87
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 40 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 87 (accept_3_5 38 40 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 40
  87 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 40 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 40 87 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 40 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 40 87 (accept_3_5 35 40 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 40 87 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 40 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 87 (Polychromatic418967fa.accept_14_5_12_3_1_3397
  33 40 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 40 87 (accept_3_5 32 40
  87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 40 87 (Polychromatic418967fa.accept_6_1_4_3_1_14
  31 40 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 40 87
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 40 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 40 87 (accept_3_5 29 40 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 40
  87 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 40 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 40 87 (Polychromatic418967fa.accept_18_9_4_15_1_555 27 40 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 40 87 (accept_3_5 26 40 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 40 87 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 40 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 40 87 (Polychromatic418967fa.accept_13_11_1_9_1_1179
  24 40 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 87 (accept_3_5 23 40
  87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 87 (Polychromatic418967fa.accept_7_1_5_3_1_268
  22 40 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 87
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 40 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 40 87 (accept_3_5 20 40 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 40
  87 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 40 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 40 87 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 40 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 87 (accept_3_5 17 40 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 40 87 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 40 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 40 87 (Polychromatic418967fa.accept_7_1_5_3_1_268 15
  40 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 40 87 (accept_3_5 14 40 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 40 87 (Polychromatic418967fa.accept_6_1_4_3_1_14 13
  40 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 40 87
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 40 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 40 87 (accept_3_5 11 40 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 40
  87 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 40 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 40 87 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 40 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 40 87 (accept_3_5 8 40 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 40 87 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 40 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 40 87 (Polychromatic418967fa.accept_12_6_4_3_1_361 6
  40 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 40 87 (accept_3_5 5 40 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 40 87 (Polychromatic418967fa.accept_16_4_8_7_1_3396 4
  40 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 87
  (Polychromatic418967fa.accept_9_3_4_6_1_252 3 40 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 40 87 (accept_3_5 2 40 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40 87
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 40 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 40 87)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 87 (allA_succ_of_accept 38 39 87
  (Polychromatic418967fa.accept_9_2_3_6_1_88 38 39 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 87 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 39 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 87 3 12 13 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 87 (Polychromatic418967fa.accept_9_8_3_6_1_533 35 39 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 87
  (Polychromatic418967fa.accept_7_6_4_3_1_266 34 39 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 39 87 3 11 13 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 39 87 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 39 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 87 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 39 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 87 3 10 13 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 87
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 39 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 87 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 39 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 87 3 9 13 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 87 (Polychromatic418967fa.accept_9_8_3_6_1_533 26 39 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 87
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 39 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 39 87 3 8 13 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 39 87 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 39 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 87 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 39 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 87 3 7 13 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 87
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 39 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 87 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 39 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 87 3 6 13 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 87 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 39 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 87
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 39 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 39 87 3 5 13 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 39 87 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 39 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 87 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 39 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 39 87 3 4 13 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 39 87
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 39 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 87 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 39 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 87 3 3 13 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 87 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 39 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 87
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 39 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 39 87 3 2 13 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 39 87 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 39 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 87 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 39 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 39 87 3 1 13 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 39 87
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 39 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 87 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 39 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 39 87))))))))))))))))))))))))))))))))))))))) (allB_succ 38 87
  (allA_succ_of_accept 37 38 87 (accept_3_4 37 38 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 38
  87 (Polychromatic418967fa.accept_13_10_12_9_1_1837 36 38 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 87 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 38 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 87 (accept_3_4 34 38 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 38 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 87
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 38 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 87 (accept_3_4 31 38 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 38
  87 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 38 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 38 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 38 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 87 (accept_3_4 28 38 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 38 87 (Polychromatic418967fa.accept_14_13_10_3_1_1037 27 38 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 87 (Polychromatic418967fa.accept_9_8_2_6_1_875 26
  38 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 38 87 (accept_3_4 25 38 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 38 87
  (Polychromatic418967fa.accept_25_24_13_12_1_3395 24 38 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 38 87 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 38 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 87 (accept_3_4 22 38 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 38 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 38 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 87 (Polychromatic418967fa.accept_14_6_10_3_1_1038
  20 38 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 38 87 (accept_3_4 19 38
  87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 38 87 (Polychromatic418967fa.accept_12_6_2_3_1_354
  18 38 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 38 87
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 38 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 38 87 (accept_3_4 16 38 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 38
  87 (Polychromatic418967fa.accept_10_5_8_7_1_2174 15 38 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 38 87 (Polychromatic418967fa.accept_9_5_2_6_1_265 14 38 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 38 87 (accept_3_4 13 38 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 38 87 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 38 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 38 87 (Polychromatic418967fa.accept_6_5_2_3_1_81 11
  38 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 87 (accept_3_4 10 38 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 38
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 87
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 38 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 87 (accept_3_4 7 38 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38 87
  (Polychromatic418967fa.accept_11_6_5_10_1_2724 6 38 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 38 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 87 (accept_3_4 4 38 87 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 38 87 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 38 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 87 (Polychromatic418967fa.accept_20_2_18_7_1_3394 2 38 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 87 (accept_3_4 1 38 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 38 87)))))))))))))))))))))))))))))))))))))) (allB_succ 37 87
  (allA_succ_of_accept 36 37 87 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 37 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 87 (accept_3_5 35 37 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 37 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 37 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 87 (Polychromatic418967fa.accept_7_5_2_3_1_106 33
  37 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 87 (accept_3_5 32 37 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 87 (Polychromatic418967fa.accept_9_4_1_6_1_284 31
  37 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 87
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 37 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 87 (accept_3_5 29 37 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 37
  87 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 37 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 37 87 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 37 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 87 (accept_3_5 26 37 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 37 87 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 37 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 87 (Polychromatic418967fa.accept_20_4_17_7_1_3393
  24 37 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 87 (accept_3_5 23 37
  87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 37 87 (Polychromatic418967fa.accept_4_2_1_3_1_27
  22 37 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 87
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 37 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 37 87 (accept_3_5 20 37 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 37
  87 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 37 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 37 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 37 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 87 (accept_3_5 17 37 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 37 87 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 37 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 87 (Polychromatic418967fa.accept_7_1_2_3_1_257 15
  37 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 87 (accept_3_5 14 37 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 87 (Polychromatic418967fa.accept_7_6_2_3_1_107 13
  37 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 87
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 37 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 87 (accept_3_5 11 37 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 37
  87 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 37 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 37 87 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 37 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 87 (accept_3_5 8 37 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 37 87 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 37 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 37
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 87 (accept_3_5 5 37 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37 87 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 37
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 87
  (Polychromatic418967fa.accept_9_3_1_6_1_86 3 37 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 37 87 (accept_3_5 2 37 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37 87
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 37 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 37 87))))))))))))))))))))))))))))))))))))) (allB_succ 36 87 (allA_succ_of_accept 35 36 87
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 36 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 87 (Polychromatic418967fa.accept_23_11_13_18_1_3392 34 36 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 36 87 3 11 12 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 36 87 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 36 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 87
  (Polychromatic418967fa.accept_10_1_6_7_1_710 31 36 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 36 87 3 10 12 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 36 87 (Polychromatic418967fa.accept_11_7_3_10_1_1461 29 36 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 87 (Polychromatic418967fa.accept_16_12_4_7_1_3391 28 36 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 36 87 3 9 12 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 36 87
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 36 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 36 87 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 36 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 87 3 8 12 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 87 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 36 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 36 87
  (Polychromatic418967fa.accept_15_7_6_12_1_1614 22 36 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 36 87 3 7 12 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 36 87 (Polychromatic418967fa.accept_15_5_6_12_1_916 20 36 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 87 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 36 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 87 3 6 12 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 87
  (Polychromatic418967fa.accept_15_2_6_12_1_1613 17 36 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 36 87 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 36 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 36 87 3 5 12 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 36 87 (Polychromatic418967fa.accept_13_1_10_9_1_215 14 36 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 87
  (Polychromatic418967fa.accept_10_3_6_7_1_2188 13 36 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 36 87 3 4 12 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 36 87 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 36 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 36 87 (Polychromatic418967fa.accept_15_10_6_12_1_1645 10 36 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 36 87 3 3 12 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 36 87
  (Polychromatic418967fa.accept_16_8_4_7_1_3390 8 36 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 36 87 (Polychromatic418967fa.accept_11_7_3_10_1_1461 7 36 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 87 3 2 12 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 87 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 36 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36 87
  (Polychromatic418967fa.accept_7_4_1_3_1_277 4 36 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 36 87 3 1 12 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 36 87 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 36 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 87 (Polychromatic418967fa.accept_10_1_6_7_1_710 1 36 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 87))))))))))))))))))))))))))))))))))))
  (allB_succ 35 87 (allA_succ_of_accept 34 35 87 (accept_3_4 34 35 87 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 35 87 (Polychromatic418967fa.accept_10_3_5_7_1_330 33 35 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 35 87 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 35 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 87 (accept_3_4 31 35 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 35 87 (Polychromatic418967fa.accept_9_3_8_6_1_80 30
  35 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 87
  (Polychromatic418967fa.accept_9_2_8_6_1_79 29 35 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 35 87 (accept_3_4 28 35 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35
  87 (Polychromatic418967fa.accept_16_11_3_7_1_2375 27 35 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 35 87 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 35 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 87 (accept_3_4 25 35 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 35 87 (Polychromatic418967fa.accept_14_10_7_3_1_1022 24 35 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 87
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 35 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 87 (accept_3_4 22 35 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35
  87 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 35 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 35 87 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 35 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 87 (accept_3_4 19 35 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 35 87 (Polychromatic418967fa.accept_10_8_5_7_1_358 18 35 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 87 (Polychromatic418967fa.accept_15_2_5_12_1_369
  17 35 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 87 (accept_3_4 16 35
  87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 87
  (Polychromatic418967fa.accept_16_15_3_7_1_3389 15 35 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 35 87 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 35 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 87 (accept_3_4 13 35 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 35 87 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 35 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 87 (Polychromatic418967fa.accept_9_2_8_6_1_79 11
  35 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 87 (accept_3_4 10 35 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 87 (Polychromatic418967fa.accept_12_9_11_3_1_772 9
  35 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 87
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 35 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 35 87 (accept_3_4 7 35 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 87
  (Polychromatic418967fa.accept_15_6_5_12_1_1642 6 35 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 35 87 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 35 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 87 (accept_3_4 4 35 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 35 87 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 35 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 87 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 35
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 87 (accept_3_4 1 35 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35 87))))))))))))))))))))))))))))))))))) (allB_succ 34 87
  (allA_succ_of_accept 33 34 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 34 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 34 87 (accept_3_5 32 34 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 34 87 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 34 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 34 87 (Polychromatic418967fa.accept_7_2_6_3_1_100 30
  34 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 87 (accept_3_5 29 34 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 87 (Polychromatic418967fa.accept_9_1_7_6_1_75 28
  34 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 87
  (Polychromatic418967fa.accept_13_1_8_9_1_1154 27 34 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 87 (accept_3_5 26 34 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 34
  87 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 34 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 34 87 (Polychromatic418967fa.accept_11_2_1_10_1_196 24 34 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 87 (accept_3_5 23 34 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 34 87 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 34 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 34
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 34 87 (accept_3_5 20 34 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 34 87 (Polychromatic418967fa.accept_6_1_4_3_1_14 19
  34 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 34 87
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 34 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 34 87 (accept_3_5 17 34 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 34
  87 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 34 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 34 87 (Polychromatic418967fa.accept_30_15_4_27_1_3388 15 34 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 34 87 (accept_3_5 14 34 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 34 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 34 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 34 87 (Polychromatic418967fa.accept_9_3_7_6_1_76 12
  34 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 87 (accept_3_5 11 34 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 87 (Polychromatic418967fa.accept_9_1_7_6_1_75 10
  34 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 87
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 34 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 87 (accept_3_5 8 34 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34 87
  (Polychromatic418967fa.accept_6_1_4_3_1_14 7 34 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 34 87 (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 34 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 87 (accept_3_5 5 34 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 34 87 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 34 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 87 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 34
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 87 (accept_3_5 2 34 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 34
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 87))))))))))))))))))))))))))))))))))
  (allB_succ 33 87 (allA_succ_of_accept 32 33 87 (Polychromatic418967fa.accept_13_6_7_9_1_1848 32 33 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 87
  (Polychromatic418967fa.accept_12_7_9_3_1_767 31 33 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 33 87 3 10 11 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 33 87 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 33 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 87 (Polychromatic418967fa.accept_13_2_7_9_1_2616 28 33 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 33 87 3 9 11 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 33 87
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 33 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 87 (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 33 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 87 3 8 11 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 87 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 33 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 87
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 33 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 33 87 3 7 11 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 33 87 (Polychromatic418967fa.accept_21_20_12_3_1_3387 20 33 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 87 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 33 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 33 87 3 6 11 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 33 87
  (Polychromatic418967fa.accept_12_5_9_3_1_85 17 33 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 87 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 33 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 87 3 5 11 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 33 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 87
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 33 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 33 87 3 4 11 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 33 87 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 33 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 33 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 33 87 3 3 11 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 33 87
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 33 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 87 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 33 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 87 3 2 11 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 87 (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 33 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 87
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 4 33 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 33 87 3 1 11 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 33 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 33 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 87 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 33 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 87)))))))))))))))))))))))))))))))))
  (allB_succ 32 87 (allA_succ_of_accept 31 32 87 (accept_3_4 31 32 87 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 32 87 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 32 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 32 87 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 32 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 87 (accept_3_4 28 32 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 32 87 (Polychromatic418967fa.accept_7_6_4_3_1_266 27
  32 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 87
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 32 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 32 87 (accept_3_4 25 32 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 32
  87 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 32 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 32 87 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 32 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 87 (accept_3_4 22 32 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 32 87 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 32 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 87 (Polychromatic418967fa.accept_7_6_4_3_1_266 20
  32 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 32 87 (accept_3_4 19 32 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 32 87 (Polychromatic418967fa.accept_12_6_8_3_1_82 18
  32 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 32 87
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 32 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 32 87 (accept_3_4 16 32 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 32
  87 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 32 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 32 87 (Polychromatic418967fa.accept_10_4_2_7_1_373 14 32 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 32 87 (accept_3_4 13 32 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 32 87 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 32 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 32 87 (Polychromatic418967fa.accept_6_5_2_3_1_81 11
  32 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 87 (accept_3_4 10 32 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 87 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9
  32 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 87
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 32 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 87 (accept_3_4 7 32 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32 87
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 32 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 32 87 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 32 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 87 (accept_3_4 4 32 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 32 87 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 32 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 87 (Polychromatic418967fa.accept_9_2_5_6_1_536 2 32
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 87 (accept_3_4 1 32 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 87)))))))))))))))))))))))))))))))) (allB_succ 31 87
  (allA_succ_of_accept 30 31 87 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 31 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 87 (accept_3_5 29 31 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 87 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 31 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 87 (Polychromatic418967fa.accept_13_1_5_9_1_226 27
  31 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 87 (accept_3_5 26 31 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 87 (Polychromatic418967fa.accept_9_7_4_6_1_273 25
  31 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 87
  (Polychromatic418967fa.accept_10_4_1_7_1_371 24 31 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 87 (accept_3_5 23 31 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 31
  87 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 31 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 31 87 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 31 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 87 (accept_3_5 20 31 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 31 87 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 31 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 87
  (Polychromatic418967fa.accept_19_18_12_11_1_3386 18 31 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 87 (accept_3_5 17 31 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 31
  87 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 31 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 31 87 (Polychromatic418967fa.accept_13_2_5_9_1_610 15 31 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 87 (accept_3_5 14 31 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 31 87 (Polychromatic418967fa.accept_15_13_1_12_1_1638 13 31 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 87 (Polychromatic418967fa.accept_9_3_4_6_1_252 12
  31 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 87 (accept_3_5 11 31 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 31 87 (Polychromatic418967fa.accept_6_4_1_3_1_77 10
  31 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 87
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 31 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 31 87 (accept_3_5 8 31 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 87
  (Polychromatic418967fa.accept_9_7_4_6_1_273 7 31 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 31 87 (Polychromatic418967fa.accept_10_6_1_7_1_342 6 31 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 31 87 (accept_3_5 5 31 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 31 87 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 31 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 31 87 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 31
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 87 (accept_3_5 2 31 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 87 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 31
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 87)))))))))))))))))))))))))))))))
  (allB_succ 30 87 (allA_succ_of_accept 29 30 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 30 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 30 87 (Polychromatic418967fa.accept_9_1_3_6_1_70 28
  30 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 30 87 3 9 10 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 30 87
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 30 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 30 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 30 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 87 3 8 10 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 87 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 30 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 87
  (Polychromatic418967fa.accept_7_1_2_3_1_257 22 30 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 30 87 3 7 10 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 30 87 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 30 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 87 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 30 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 87 3 6 10 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 87
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 30 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 30 87 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 30 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 30 87 3 5 10 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 30 87 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 30 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 87
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 30 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 30 87 3 4 10 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 30 87 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 30 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 30 87 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 30 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 30 87 3 3 10 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 30 87
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 30 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 30 87 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 30 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 87 3 2 10 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 30 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30 87
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 30 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 30 87 3 1 10 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 30 87 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 30 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 30 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 87)))))))))))))))))))))))))))))) (allB_succ
  29 87 (allA_succ_of_accept 28 29 87 (accept_3_4 28 29 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 29 87 (Polychromatic418967fa.accept_17_10_12_2_1_3385 27 29 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 29 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 29 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 87 (accept_3_4 25 29 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 29 87 (Polychromatic418967fa.accept_15_9_14_12_1_913 24 29 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 87
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 29 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 87 (accept_3_4 22 29 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29
  87 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 29 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 29 87 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 29 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 87 (accept_3_4 19 29 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 29 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 29 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 87 (Polychromatic418967fa.accept_9_8_2_6_1_875 17
  29 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 87 (accept_3_4 16 29 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 87 (Polychromatic418967fa.accept_13_2_3_9_1_2610
  15 29 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 87
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 29 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 29 87 (accept_3_4 13 29 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 29
  87 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 29 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 29 87 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 29 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 87 (accept_3_4 10 29 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 29 87 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 29 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 87 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 29
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 87 (accept_3_4 7 29 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 29
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 87
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 29 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 87 (accept_3_4 4 29 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29 87
  (Polychromatic418967fa.accept_9_3_2_6_1_264 3 29 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 29 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 87 (accept_3_4 1 29 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 87))))))))))))))))))))))))))))) (allB_succ 28 87 (allA_succ_of_accept 27 28 87
  (Polychromatic418967fa.accept_8_3_4_7_1_475 27 28 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 28 87 (accept_3_5 26 28 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 28
  87 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 28 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 28 87 (Polychromatic418967fa.accept_13_11_2_9_1_2640 24 28 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 87 (accept_3_5 23 28 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 28 87 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 28 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 28 87 (Polychromatic418967fa.accept_9_3_1_6_1_86 21
  28 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 28 87 (accept_3_5 20 28 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 28 87 (Polychromatic418967fa.accept_6_1_4_3_1_14 19
  28 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 28 87
  (Polychromatic418967fa.accept_12_6_4_3_1_361 18 28 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 28 87 (accept_3_5 17 28 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 28
  87 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 28 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 28 87 (Polychromatic418967fa.accept_10_5_8_7_1_2174 15 28 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 28 87 (accept_3_5 14 28 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 28 87 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 28 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 28 87 (Polychromatic418967fa.accept_9_3_1_6_1_86 12
  28 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 28 87 (accept_3_5 11 28 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 28 87
  (Polychromatic418967fa.accept_15_10_13_12_1_3384 10 28 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 28 87 (Polychromatic418967fa.accept_10_9_8_7_1_714 9 28 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 28 87 (accept_3_5 8 28 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 28 87 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 28 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 28 87 (Polychromatic418967fa.accept_12_6_4_3_1_361 6
  28 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 28 87 (accept_3_5 5 28 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 28 87 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 28
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 28 87
  (Polychromatic418967fa.accept_8_3_4_7_1_475 3 28 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 28 87 (accept_3_5 2 28 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 28 87
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 28 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 28 87)))))))))))))))))))))))))))) (allB_succ 27 87 (allA_succ_of_accept 26 27 87
  (Polychromatic418967fa.accept_11_4_5_10_1_926 26 27 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 87 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 27 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 27 87 3 8 9 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 27 87 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 27 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 87
  (Polychromatic418967fa.accept_18_4_9_15_1_3383 22 27 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 27 87 3 7 9 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 27 87 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 27 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 87 (Polychromatic418967fa.accept_13_6_1_9_1_619 19 27 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 27 87 3 6 9 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 27 87
  (Polychromatic418967fa.accept_11_6_5_10_1_2724 17 27 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 27 87 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 27 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 27 87 3 5 9 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 27 87 (Polychromatic418967fa.accept_21_14_6_3_1_3382 14 27 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 87
  (Polychromatic418967fa.accept_21_13_6_3_1_3381 13 27 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 27 87 3 4 9 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 27 87 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 27 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 87 (Polychromatic418967fa.accept_13_10_1_9_1_3380 10 27 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 27 87 3 3 9 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 27 87
  (Polychromatic418967fa.accept_13_8_1_9_1_1178 8 27 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 87 (Polychromatic418967fa.accept_19_7_8_11_1_3379 7 27 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 27 87 3 2 9 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 27 87 (Polychromatic418967fa.accept_13_5_1_9_1_618 5 27 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 87
  (Polychromatic418967fa.accept_7_4_6_3_1_271 4 27 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 27 87 3 1 9 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 27 87 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 27 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 87 (Polychromatic418967fa.accept_19_1_8_11_1_3378 1 27 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 87))))))))))))))))))))))))))) (allB_succ 26
  87 (allA_succ_of_accept 25 26 87 (accept_3_4 25 26 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  26 87 (Polychromatic418967fa.accept_17_7_9_2_1_629 24 26 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 26 87 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 26 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 87 (accept_3_4 22 26 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 26 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 26 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 87
  (Polychromatic418967fa.accept_9_2_8_6_1_79 20 26 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 26 87 (accept_3_4 19 26 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 26
  87 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 26 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 26 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 26 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 87 (accept_3_4 16 26 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 26 87 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 26 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 87 (Polychromatic418967fa.accept_9_5_8_6_1_281 14
  26 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 26 87 (accept_3_4 13 26 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 26 87 (Polychromatic418967fa.accept_9_3_8_6_1_80 12
  26 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 26 87
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 26 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 26 87 (accept_3_4 10 26 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 26
  87 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 26 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 26 87 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 26 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 26 87 (accept_3_4 7 26 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 26 87 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 26 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 26 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 26
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 87 (accept_3_4 4 26 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 26 87 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 26
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 87
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 26 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 26 87 (accept_3_4 1 26 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  87)))))))))))))))))))))))))) (allB_succ 25 87 (allA_succ_of_accept 24 25 87
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 24 25 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 87 (accept_3_5 23 25 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 25
  87 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 25 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 25 87 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 25 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 87 (accept_3_5 20 25 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 25 87 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 25 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 18
  25 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 87 (accept_3_5 17 25 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 25 87 (Polychromatic418967fa.accept_6_4_1_3_1_77 16
  25 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 25 87
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 25 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 25 87 (accept_3_5 14 25 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 25
  87 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 25 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 25 87 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 25 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 87 (accept_3_5 11 25 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 25 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 25 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 25 87 (Polychromatic418967fa.accept_12_9_1_3_1_350 9
  25 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 87 (accept_3_5 8 25 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 87 (Polychromatic418967fa.accept_11_7_3_10_1_1461 7
  25 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 87
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 25 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 87 (accept_3_5 5 25 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25 87
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 25 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 25 87 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 25 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 87 (accept_3_5 2 25 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 25 87 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 25 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 87))))))))))))))))))))))))) (allB_succ 24 87
  (allA_succ_of_accept 23 24 87 (Polychromatic418967fa.accept_10_3_4_7_1_353 23 24 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 87 (Polychromatic418967fa.accept_10_2_4_7_1_352 22 24 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 24 87 3 7 8 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 24 87
  (Polychromatic418967fa.accept_13_7_11_9_1_1858 20 24 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 24 87 (Polychromatic418967fa.accept_15_4_9_12_1_2495 19 24 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 87 3 6 8 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 87 (Polychromatic418967fa.accept_16_1_8_7_1_3377 17 24 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 87
  (Polychromatic418967fa.accept_18_16_6_15_1_3376 16 24 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 24 87 3 5 8 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 24 87 (Polychromatic418967fa.accept_13_1_11_9_1_1857 14 24 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 87 (Polychromatic418967fa.accept_10_3_4_7_1_353 13 24 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 87 3 4 8 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 87
  (Polychromatic418967fa.accept_10_1_4_7_1_374 11 24 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 24 87 (Polychromatic418967fa.accept_15_10_9_12_1_2497 10 24 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 24 87 3 3 8 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 24 87 (Polychromatic418967fa.accept_13_8_11_9_1_593 8 24 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 87
  (Polychromatic418967fa.accept_13_7_11_9_1_1858 7 24 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 24 87 3 2 8 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 24 87 (Polychromatic418967fa.accept_15_5_9_12_1_1599 5 24 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 87 (Polychromatic418967fa.accept_15_4_9_12_1_2495 4 24 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 24 87 3 1 8 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 24 87
  (Polychromatic418967fa.accept_10_2_4_7_1_352 2 24 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 24 87 (Polychromatic418967fa.accept_10_1_4_7_1_374 1 24 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 24 87)))))))))))))))))))))))) (allB_succ 23 87 (allA_succ_of_accept 22 23 87
  (accept_3_4 22 23 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 87
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 23 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 87 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 23 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 87 (accept_3_4 19 23 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 87 (Polychromatic418967fa.accept_15_3_8_12_1_900 18 23 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 87 (Polychromatic418967fa.accept_9_8_5_6_1_538 17
  23 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 87 (accept_3_4 16 23 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 87 (Polychromatic418967fa.accept_7_1_2_3_1_257 15
  23 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 87
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 23 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 87 (accept_3_4 13 23 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 23
  87 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 23 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 23 87 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 23 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 87 (accept_3_4 10 23 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 23 87 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 23 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 87 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 23
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 87 (accept_3_4 7 23 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 87 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 23
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 87
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 23 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 87 (accept_3_4 4 23 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23 87
  (Polychromatic418967fa.accept_9_3_5_6_1_253 3 23 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 23 87 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 23 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 87 (accept_3_4 1 23 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 23 87))))))))))))))))))))))) (allB_succ 22 87 (allA_succ_of_accept 21 22 87
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 22 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 87 (accept_3_5 20 22 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 22
  87 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 22 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 22 87 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 22 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 87 (accept_3_5 17 22 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 22 87 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 22 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 87 (Polychromatic418967fa.accept_10_5_2_7_1_345 15
  22 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 22 87 (accept_3_5 14 22 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 22 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 22
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 22 87
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 22 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 22 87 (accept_3_5 11 22 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 22
  87 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 22 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 22 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 22 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 8 22 87 (accept_3_5 8 22 87 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 22 87 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 22 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 22 87 (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 22 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 87 (accept_3_5 5 22 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 22 87 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 22 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 87
  (Polychromatic418967fa.accept_9_3_4_6_1_252 3 22 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 22 87 (accept_3_5 2 22 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 87
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 22 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 22 87)))))))))))))))))))))) (allB_succ 21 87 (allA_succ_of_accept 20 21 87
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 21 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 87 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 21 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 87 3 6 7 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 87 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 21 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 87
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 21 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 21 87 3 5 7 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 21 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 21 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 87 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 21 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 21 87 3 4 7 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 21 87
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 21 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 21 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 87 3 3 7 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 87 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 21 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 87
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 21 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 21 87 3 2 7 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 21 87 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 21 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 87 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 21 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 21 87 3 1 7 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 21 87
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 21 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 21 87 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 21 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 21 87))))))))))))))))))))) (allB_succ 20 87 (allA_succ_of_accept 19 20 87
  (accept_3_4 19 20 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 87
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 20 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 20 87 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 20 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 87 (accept_3_4 16 20 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 20 87 (Polychromatic418967fa.accept_13_2_7_9_1_2616 15 20 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 20 87 (Polychromatic418967fa.accept_9_5_2_6_1_265 14
  20 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 87 (accept_3_4 13 20 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 87 (Polychromatic418967fa.accept_9_3_2_6_1_264 12
  20 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 20 87
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 20 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 20 87 (accept_3_4 10 20 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 20
  87 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 20 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 20 87 (Polychromatic418967fa.accept_9_8_2_6_1_875 8 20 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 87 (accept_3_4 7 20 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 20 87 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 20 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 20 87 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 20
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 20 87 (accept_3_4 4 20 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20 87 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 20
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 20 87
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 20 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 20 87 (accept_3_4 1 20 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20
  87)))))))))))))))))))) (allB_succ 19 87 (allA_succ_of_accept 18 19 87 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18
  19 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 19 87 (accept_3_5 17 19 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 19 87 (Polychromatic418967fa.accept_6_4_1_3_1_77 16
  19 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 19 87
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 19 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 19 87 (accept_3_5 14 19 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 19
  87 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 19 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 19 87 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 19 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 19 87 (accept_3_5 11 19 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 19 87 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 19 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 19 87 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 19
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 87 (accept_3_5 8 19 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 87 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 19
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 87
  (Polychromatic418967fa.accept_20_6_19_7_1_3375 6 19 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 87 (accept_3_5 5 19 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19 87
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 19 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 87 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 19 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 87 (accept_3_5 2 19 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 87 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 19 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 87))))))))))))))))))) (allB_succ 18 87 (allA_succ_of_accept 17
  18 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 18 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 18 87 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 18 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 18 87 3 5 6 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 18 87 (Polychromatic418967fa.accept_11_3_7_10_1_180 14 18 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 18 87
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 18 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 18 87 3 4 6 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 18 87 (Polychromatic418967fa.accept_16_11_2_7_1_3374 11 18 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 87 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 18 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 18 87 3 3 6 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 18 87
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 18 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 87 (Polychromatic418967fa.accept_14_7_4_3_1_488 7 18 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 87 3 2 6 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 18 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 87
  (Polychromatic418967fa.accept_12_4_6_3_1_332 4 18 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 18 87 3 1 6 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 18 87 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 18 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 18 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 87)))))))))))))))))) (allB_succ 17 87
  (allA_succ_of_accept 16 17 87 (accept_3_4 16 17 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17
  87 (Polychromatic418967fa.accept_21_15_17_3_1_3373 15 17 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 17 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 17 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 87 (accept_3_4 13 17 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 17 87 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 17 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 87
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 17 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 17 87 (accept_3_4 10 17 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 17
  87 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 17 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 17 87 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 17 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 87 (accept_3_4 7 17 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 17 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 17 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 87 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 17
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 87 (accept_3_4 4 17 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17 87 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 17
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 87
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 17 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 17 87 (accept_3_4 1 17 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17
  87))))))))))))))))) (allB_succ 16 87 (allA_succ_of_accept 15 16 87 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 16
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 16 87 (accept_3_5 14 16 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 16 87 (Polychromatic418967fa.accept_6_1_4_3_1_14 13
  16 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 16 87
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 16 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 16 87 (accept_3_5 11 16 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 16
  87 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 16 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 16 87 (Polychromatic418967fa.accept_18_9_16_15_1_2241 9 16 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 16 87 (accept_3_5 8 16 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 16 87 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 16 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 16 87 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 16
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 16 87 (accept_3_5 5 16 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 16 87 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 16
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 16 87
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 16 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 16 87 (accept_3_5 2 16 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 16 87
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 16 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 16 87)))))))))))))))) (allB_succ 15 87 (allA_succ_of_accept 14 15 87
  (Polychromatic418967fa.accept_13_1_2_9_1_1186 14 15 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 87 (Polychromatic418967fa.accept_10_3_5_7_1_330 13 15 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 87 3 4 5 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 87 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 15 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 87
  (Polychromatic418967fa.accept_17_10_15_2_1_653 10 15 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 15 87 3 3 5 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 15 87 (Polychromatic418967fa.accept_10_8_5_7_1_358 8 15 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 87 (Polychromatic418967fa.accept_13_7_2_9_1_1826 7 15 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 15 87 3 2 5 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 15 87
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 15 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 15 87 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 15 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 87 3 1 5 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 87 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 15 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 87
  (Polychromatic418967fa.accept_13_1_2_9_1_1186 1 15 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 15 87))))))))))))))) (allB_succ 14 87 (allA_succ_of_accept 13 14 87 (accept_3_4 13 14 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 87 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 14 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 14 87
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 14 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 14 87 (accept_3_4 10 14 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 14
  87 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 14 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 14 87 (Polychromatic418967fa.accept_9_8_5_6_1_538 8 14 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 87 (accept_3_4 7 14 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 14 87 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 14 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 14
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 14 87 (accept_3_4 4 14 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14 87 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 14
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 14 87
  (Polychromatic418967fa.accept_9_2_5_6_1_536 2 14 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 14 87 (accept_3_4 1 14 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14
  87)))))))))))))) (allB_succ 13 87 (allA_succ_of_accept 12 13 87 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 13 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 13 87 (accept_3_5 11 13 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 13 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 10
  13 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 13 87
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 13 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 13 87 (accept_3_5 8 13 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 87
  (Polychromatic418967fa.accept_9_7_4_6_1_273 7 13 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 13 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 13 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 13 87 (accept_3_5 5 13 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 13 87 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 13 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 13 87 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 13
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 87 (accept_3_5 2 13 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 87 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 13
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 87))))))))))))) (allB_succ 12 87
  (allA_succ_of_accept 11 12 87 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 12 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 87 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 12 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 12 87 3 3 4 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 12 87
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 12 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 12 87 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 12 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 87 3 2 4 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 87 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 12 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 87
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 12 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 12 87 3 1 4 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 12 87 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 12 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 87 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 12 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 87)))))))))))) (allB_succ 11 87
  (allA_succ_of_accept 10 11 87 (accept_3_4 10 11 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11
  87 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 11 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 87 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 11 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 87 (accept_3_4 7 11 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 87 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 11 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 87 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 11
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 87 (accept_3_4 4 11 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 87 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 11
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 87
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 11 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 87 (accept_3_4 1 11 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11 87)))))))))))
  (allB_succ 10 87 (allA_succ_of_accept 9 10 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 10 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 10 87 (accept_3_5 8 10 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 10 87 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 10 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 10 87 (Polychromatic418967fa.accept_12_6_10_3_1_1313 6
  10 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 10 87 (accept_3_5 5 10 87
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 10 87 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 10
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 10 87
  (Polychromatic418967fa.accept_9_3_1_6_1_86 3 10 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 10 87 (accept_3_5 2 10 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 10 87
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 10 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 10 87)))))))))) (allB_succ 9 87 (allA_succ_of_accept 8 9 87 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 9
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 87
  (Polychromatic418967fa.accept_12_7_9_3_1_767 7 9 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 9 87 3 2 3 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 9 87 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 9 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 87 (Polychromatic418967fa.accept_15_4_9_12_1_2495 4 9 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 9 87 3 1 3 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 9 87
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 9 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 87 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 9 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 9 87))))))))) (allB_succ 8 87 (allA_succ_of_accept 7 8 87 (accept_3_4 7 8 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 87 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 8 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 8 87
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 8 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 8 87 (accept_3_4 4 8 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 8 87
  (Polychromatic418967fa.accept_9_3_8_6_1_80 3 8 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 8 87 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 8 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 87 (accept_3_4 1 8 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one
  8 87)))))))) (allB_succ 7 87 (allA_succ_of_accept 6 7 87 (Polychromatic418967fa.accept_13_6_7_9_1_1848 6 7 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 7 87 (accept_3_5 5 7 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 87 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 7 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 7 87 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 7 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 87 (accept_3_5 2 7 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 7 87 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 7 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 87))))))) (allB_succ 6 87 (allA_succ_of_accept 5 6 87
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 6 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 87 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 6 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 3 6 87 3 1 2 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 2 6 87 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 6 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 87 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 6 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 87)))))) (allB_succ 5 87 (allA_succ_of_accept
  4 5 87 (accept_3_4 4 5 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 87
  (Polychromatic418967fa.accept_9_3_5_6_1_253 3 5 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 5 87 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 5 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 87 (accept_3_4 1 5 87 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one
  5 87))))) (allB_succ 4 87 (allA_succ_of_accept 3 4 87 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 4 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 4 87 (accept_3_5 2 4 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 87 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 4 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 4 87)))) (allB_succ 3 87 (allA_succ_of_accept 2 3 87
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 3 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 87 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 3 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 3 87))) (allB_succ 2 87 (allA_succ_of_accept 1 2 87 (accept_3_4 1 2 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 2 87)) (allB_two
  87)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


