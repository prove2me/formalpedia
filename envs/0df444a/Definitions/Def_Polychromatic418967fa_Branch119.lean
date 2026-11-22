-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch119
-- name    : Polychromatic418967fa_Branch119
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:11:49.241227+00:00
-- url     : https://prove2.me/theorems/4881437c-5f2f-49d9-9cfb-9f2d97653f14
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

def Polychromatic418967fa.branch_119 : allB 119 119 :=
  allB_succ' 2 118 119 (Eq.refl Bool.true) (allA_of_3_0 2 118 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  117 119 (Eq.refl Bool.true) (allA_succ_of_accept 2 117 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 117 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 119 (accept_3_2 1 117 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117 119))) (allB_succ' 4 116 119 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 116 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 116 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 116 119 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 116 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 116 119 (accept_3_2 1 116 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116 119)))) (allB_succ' 5 115 119 (Eq.refl Bool.true) (allA_of_3_0
  5 115 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 6 114 119 (Eq.refl Bool.true) (allA_succ_of_accept 5
  114 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 114 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 114 119 (accept_3_2 4 114 119 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 114 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 114 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 114 119 (Polychromatic418967fa.accept_11_2_4_9_1_484 2 114 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 119 (accept_3_2 1 114 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114 119)))))) (allB_succ' 7 113 119 (Eq.refl Bool.true)
  (allA_succ_of_accept 6 113 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 113 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 113 119 (Polychromatic418967fa.accept_13_5_9_2_1_1489 5 113 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 119 (accept_3_2 4 113 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 119 (Polychromatic418967fa.accept_9_3_5_2_1_28 3
  113 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 119
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 113 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 119 (accept_3_2 1 113 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113 119)))))))
  (allB_succ' 8 112 119 (Eq.refl Bool.true) (allA_of_3_0 8 112 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  9 111 119 (Eq.refl Bool.true) (allA_succ_of_accept 8 111 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 111 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 119 (accept_3_2 7 111 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 119 (Polychromatic418967fa.accept_9_6_3_2_1_431 6
  111 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 119
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 111 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 119 (accept_3_2 4 111 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  111 119 (Polychromatic418967fa.accept_16_3_15_7_1_3417 3 111 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 111 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 111 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 119 (accept_3_2 1 111 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 111 119))))))))) (allB_succ' 10 110 119 (Eq.refl Bool.true) (allA_succ_of_accept 9 110
  119 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 110 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 110 119 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 110 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 110 119 (accept_3_2 7 110 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 110 119 (Polychromatic418967fa.accept_15_6_5_14_1_429 6 110 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 110 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 5
  110 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 110 119 (accept_3_2 4 110
  119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 110 119 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 110 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 110 119
  (Polychromatic418967fa.accept_14_2_12_7_1_617 2 110 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 110 119 (accept_3_2 1 110 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  119)))))))))) (allB_succ' 11 109 119 (Eq.refl Bool.true) (allA_of_3_0 11 109 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 108 119 (Eq.refl Bool.true) (allA_succ_of_accept 11 108 119
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 108 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 108 119 (accept_3_2 10 108 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  108 119 (Polychromatic418967fa.accept_19_9_13_5_1_4351 9 108 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 108 119 (Polychromatic418967fa.accept_16_8_12_7_1_2399 8 108 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 108 119 (accept_3_2 7 108 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 108 119 (Polychromatic418967fa.accept_13_6_4_2_1_1433 6 108 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 108 119
  (Polychromatic418967fa.accept_13_5_4_2_1_846 5 108 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 108 119 (accept_3_2 4 108 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  108 119 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 108 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 108 119 (Polychromatic418967fa.accept_15_2_3_14_1_972 2 108 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 108 119 (accept_3_2 1 108 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 108 119)))))))))))) (allB_succ' 13 107 119 (Eq.refl Bool.true) (allA_succ_of_accept 12
  107 119 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 107 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 107 119 (Polychromatic418967fa.accept_13_11_3_2_1_863 11 107 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 119 (accept_3_2 10 107 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 119 (Polychromatic418967fa.accept_13_9_3_2_1_399 9 107 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 119
  (Polychromatic418967fa.accept_10_8_7_9_1_425 8 107 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 107 119 (accept_3_2 7 107 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 119 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 107 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 119 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 107 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 119 (accept_3_2 4 107 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 119 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 107 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 119
  (Polychromatic418967fa.accept_10_2_7_9_1_783 2 107 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 119 (accept_3_2 1 107 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  119))))))))))))) (allB_succ' 14 106 119 (Eq.refl Bool.true) (allA_of_3_0 14 106 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 105 119 (Eq.refl Bool.true) (allA_succ_of_gcd 14 105 119 7 2 15 17 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 105 119 (accept_3_2 13 105 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 119 (Polychromatic418967fa.accept_9_3_6_2_1_160
  12 105 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 119
  (Polychromatic418967fa.accept_10_1_5_9_1_157 11 105 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 105 119 (accept_3_2 10 105 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  105 119 (Polychromatic418967fa.accept_13_9_1_2_1_2952 9 105 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 105 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 105 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 105 119 7 1 15 17 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 105 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 6
  105 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 119
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 105 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 105 119 (accept_3_2 4 105 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  105 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 105 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 105 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 105 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 119 (accept_3_2 1 105 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 105 119))))))))))))))) (allB_succ' 16 104 119 (Eq.refl Bool.true) (allA_succ_of_accept
  15 104 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 104 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 104 119 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 104 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 104 119 (accept_3_2 13 104 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 104 119 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 104 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 104 119
  (Polychromatic418967fa.accept_21_11_20_14_1_4179 11 104 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 104 119 (accept_3_2 10 104 119 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 104 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 104 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 104 119 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 104 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 104 119 (accept_3_2 7 104 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 104 119 (Polychromatic418967fa.accept_9_6_5_2_1_421 6
  104 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 104 119
  (Polychromatic418967fa.accept_10_5_4_9_1_420 5 104 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 104 119 (accept_3_2 4 104 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  104 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 104 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 104 119 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 104 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 104 119 (accept_3_2 1 104 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 104 119)))))))))))))))) (allB_succ' 17 103 119 (Eq.refl Bool.true) (allA_of_3_0 17 103
  119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 18 102 119 (Eq.refl Bool.true) (allA_succ_of_gcd 17 102 119
  17 1 6 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 16 102
  119 (accept_3_2 16 102 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 102 119
  (Polychromatic418967fa.accept_9_6_3_2_1_431 15 102 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 102 119 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 102 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 102 119 (accept_3_2 13 102 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 102 119 (Polychromatic418967fa.accept_19_12_7_5_1_5725 12 102 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 102 119
  (Polychromatic418967fa.accept_10_1_2_9_1_152 11 102 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 102 119 (accept_3_2 10 102 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  102 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 102 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 102 119 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 102 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 119 (accept_3_2 7 102 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 102 119 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 102 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 102 119
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 102 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 102 119 (accept_3_2 4 102 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  102 119 (Polychromatic418967fa.accept_13_3_11_2_1_1422 3 102 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 102 119 (Polychromatic418967fa.accept_15_2_12_14_1_1709 2 102 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 119 (accept_3_2 1 102 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 102 119)))))))))))))))))) (allB_succ' 19 101 119 (Eq.refl Bool.true)
  (allA_succ_of_accept 18 101 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 101 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 101 119 (Polychromatic418967fa.accept_24_17_5_23_1_5724 17 101
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 119 (accept_3_2 16 101
  119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 119
  (Polychromatic418967fa.accept_10_5_1_9_1_791 15 101 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 101 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 101 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 101 119 (accept_3_2 13 101 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 101 119 (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 101 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 101 119
  (Polychromatic418967fa.accept_13_11_10_2_1_3840 11 101 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 101 119 (accept_3_2 10 101 119 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 101 119 (Polychromatic418967fa.accept_21_9_17_14_1_603 9 101 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 119 (Polychromatic418967fa.accept_10_8_1_9_1_413 8 101 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 101 119 (accept_3_2 7 101 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 101 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 6
  101 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 101 119
  (Polychromatic418967fa.accept_10_5_1_9_1_791 5 101 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 101 119 (accept_3_2 4 101 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  101 119 (Polychromatic418967fa.accept_13_3_10_2_1_381 3 101 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 101 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 101 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 101 119 (accept_3_2 1 101 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 101 119))))))))))))))))))) (allB_succ' 20 100 119 (Eq.refl Bool.true) (allA_of_3_0 20
  100 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 99 119 (Eq.refl Bool.true) (allA_succ_of_accept 20 99
  119 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 99 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 119 (accept_3_2 19 99 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  99 119 (Polychromatic418967fa.accept_19_18_4_5_1_5723 18 99 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 99 119 (Polychromatic418967fa.accept_21_17_15_14_1_5707 17 99 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 119 (accept_3_2 16 99 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 119 (Polychromatic418967fa.accept_16_15_3_7_1_3389 15 99
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 99 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 99 119 (accept_3_2 13 99 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  99 119 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 99 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 99 119 (Polychromatic418967fa.accept_16_11_3_7_1_2375 11 99 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 119 (accept_3_2 10 99 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 119 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 99 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 99 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 119 (accept_3_2 7 99 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99
  119 (Polychromatic418967fa.accept_13_6_8_2_1_1484 6 99 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 99 119 (Polychromatic418967fa.accept_15_5_9_14_1_1724 5 99 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 119 (accept_3_2 4 99 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 119 (Polychromatic418967fa.accept_21_3_15_14_1_5722 3 99 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 99 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 99 119 (accept_3_2 1 99 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  119))))))))))))))))))))) (allB_succ' 22 98 119 (Eq.refl Bool.true) (allA_succ_of_gcd 21 98 119 7 3 14 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 98 119
  (Polychromatic418967fa.accept_12_8_2_11_1_246 20 98 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 98 119 (accept_3_2 19 98 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  98 119 (Polychromatic418967fa.accept_13_5_7_2_1_852 18 98 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 98 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 98 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 119 (accept_3_2 16 98 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 98 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 98 119 7 2 14 17 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 98 119 (accept_3_2 13 98 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 98 119 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 98 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 98 119
  (Polychromatic418967fa.accept_10_1_8_9_1_787 11 98 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 98 119 (accept_3_2 10 98 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  98 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 98 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 98 119 (Polychromatic418967fa.accept_11_8_10_9_1_1401 8 98 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 98 119 7 1 14 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 98 119 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 98 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 98 119
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 98 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 98 119 (accept_3_2 4 98 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 98
  119 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 98 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 98 119 (Polychromatic418967fa.accept_19_2_3_5_1_5721 2 98 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 98 119 (accept_3_2 1 98 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 98 119)))))))))))))))))))))) (allB_succ' 23 97 119 (Eq.refl Bool.true) (allA_of_3_0 23 97 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 96 119 (Eq.refl Bool.true) (allA_succ_of_accept 23 96 119
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 96 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 96 119 (accept_3_2 22 96 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  96 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 96 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 96 119 (Polychromatic418967fa.accept_13_7_5_2_1_401 20 96 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 119 (accept_3_2 19 96 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 96 119 (Polychromatic418967fa.accept_19_18_1_5_1_5720 18 96 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 96 119
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 96 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 96 119 (accept_3_2 16 96 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  96 119 (Polychromatic418967fa.accept_10_5_6_9_1_2235 15 96 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 96 119 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 96 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 119 (accept_3_2 13 96 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 96 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 96 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 96 119
  (Polychromatic418967fa.accept_21_11_12_14_1_5670 11 96 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 96 119 (accept_3_2 10 96 119 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 96 119 (Polychromatic418967fa.accept_13_9_5_2_1_2185 9 96 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 96 119 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 96 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 119 (accept_3_2 7 96 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 96 119 (Polychromatic418967fa.accept_19_6_1_5_1_5719 6
  96 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 96 119
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 96 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 96 119 (accept_3_2 4 96 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 96
  119 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 96 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 96 119 (Polychromatic418967fa.accept_14_2_12_7_1_617 2 96 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 119 (accept_3_2 1 96 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 96 119)))))))))))))))))))))))) (allB_succ' 25 95 119 (Eq.refl Bool.true) (allA_succ_of_accept 24
  95 119 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 95 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 95 119 (Polychromatic418967fa.accept_15_8_5_14_1_986 23 95 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 95 119 (accept_3_2 22 95 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 95 119 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 95 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 95 119
  (Polychromatic418967fa.accept_21_20_11_14_1_5718 20 95 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 95 119 (accept_3_2 19 95 119 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 95 119 (Polychromatic418967fa.accept_13_5_4_2_1_846 18 95 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 119 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 95 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 95 119 (accept_3_2 16 95 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 95 119 (Polychromatic418967fa.accept_9_6_5_2_1_421 15
  95 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 95 119
  (Polychromatic418967fa.accept_10_4_5_9_1_1231 14 95 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 95 119 (accept_3_2 13 95 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  95 119 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 95 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 95 119 (Polychromatic418967fa.accept_10_1_5_9_1_157 11 95 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 95 119 (accept_3_2 10 95 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 95 119 (Polychromatic418967fa.accept_15_9_5_14_1_973 9 95 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 95 119
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 95 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 95 119 (accept_3_2 7 95 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95
  119 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 95 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 95 119 (Polychromatic418967fa.accept_11_5_7_9_1_2696 5 95 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 95 119 (accept_3_2 4 95 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 95 119 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 95 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 119 (Polychromatic418967fa.accept_11_2_7_9_1_890 2
  95 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 119 (accept_3_2 1 95 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95 119))))))))))))))))))))))))) (allB_succ' 26 94 119 (Eq.refl
  Bool.true) (allA_of_3_0 26 94 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 93 119 (Eq.refl Bool.true)
  (allA_succ_of_accept 26 93 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 93 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 119 (accept_3_2 25 93 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 93 119 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 93 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 119 (Polychromatic418967fa.accept_9_5_3_2_1_171 23
  93 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 119 (accept_3_2 22 93
  119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 119
  (Polychromatic418967fa.accept_19_2_17_5_1_5643 21 93 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 93 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 93 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 119 (accept_3_2 19 93 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 93 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 93 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 119 (Polychromatic418967fa.accept_9_8_3_2_1_417 17
  93 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 119 (accept_3_2 16 93
  119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 119
  (Polychromatic418967fa.accept_9_6_3_2_1_431 15 93 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 93 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 93 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 119 (accept_3_2 13 93 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 93 119 (Polychromatic418967fa.accept_14_12_9_7_1_2762 12 93 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 119
  (Polychromatic418967fa.accept_15_11_3_14_1_971 11 93 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 93 119 (accept_3_2 10 93 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  93 119 (Polychromatic418967fa.accept_16_9_13_7_1_1509 9 93 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 93 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 93 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 119 (accept_3_2 7 93 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 93 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 93 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 119
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 93 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 93 119 (accept_3_2 4 93 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93
  119 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 93 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 93 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 93 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 119 (accept_3_2 1 93 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 93 119))))))))))))))))))))))))))) (allB_succ' 28 92 119 (Eq.refl Bool.true)
  (allA_succ_of_accept 27 92 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 92 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 92 119 (Polychromatic418967fa.accept_12_2_8_11_1_31 26 92 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 92 119 (accept_3_2 25 92 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 92 119 (Polychromatic418967fa.accept_11_2_4_9_1_484
  24 92 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 92 119
  (Polychromatic418967fa.accept_21_2_8_14_1_4148 23 92 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 92 119 (accept_3_2 22 92 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  92 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 92 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 92 119 (Polychromatic418967fa.accept_14_6_8_7_1_589 20 92 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 92 119 (accept_3_2 19 92 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 92 119 (Polychromatic418967fa.accept_15_3_2_14_1_1713 18 92 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 92 119
  (Polychromatic418967fa.accept_10_7_2_9_1_775 17 92 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 92 119 (accept_3_2 16 92 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  92 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 92 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 92 119 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 92 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 92 119 (accept_3_2 13 92 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 92 119 (Polychromatic418967fa.accept_13_12_1_2_1_845 12 92 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 92 119
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 92 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 92 119 (accept_3_2 10 92 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  92 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 92 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 92 119 (Polychromatic418967fa.accept_16_8_12_7_1_2399 8 92 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 92 119 (accept_3_2 7 92 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 92 119 (Polychromatic418967fa.accept_13_6_1_2_1_1464 6 92 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 92 119
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 5 92 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 92 119 (accept_3_2 4 92 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 92
  119 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 92 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 92 119 (Polychromatic418967fa.accept_11_2_4_9_1_484 2 92 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 119 (accept_3_2 1 92 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 92 119)))))))))))))))))))))))))))) (allB_succ' 29 91 119 (Eq.refl Bool.true) (allA_of_3_0 29 91
  119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 90 119 (Eq.refl Bool.true) (allA_succ_of_accept 29 90 119
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 90 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 90 119 (accept_3_2 28 90 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  90 119 (Polychromatic418967fa.accept_13_1_12_2_1_384 27 90 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 90 119 (Polychromatic418967fa.accept_11_4_2_9_1_496 26 90 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 119 (accept_3_2 25 90 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 90 119 (Polychromatic418967fa.accept_21_3_6_14_1_5717 24 90 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 90 119
  (Polychromatic418967fa.accept_13_10_12_2_1_1460 23 90 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 90 119 (accept_3_2 22 90 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  90 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 90 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 90 119 (Polychromatic418967fa.accept_21_20_6_14_1_5716 20 90 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 119 (accept_3_2 19 90 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 90 119 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 90 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 90 119
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 90 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 90 119 (accept_3_2 16 90 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  90 119 (Polychromatic418967fa.accept_11_4_2_9_1_496 15 90 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 90 119 (Polychromatic418967fa.accept_13_1_12_2_1_384 14 90 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 119 (accept_3_2 13 90 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 90 119 (Polychromatic418967fa.accept_21_12_6_14_1_4146 12 90 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 90 119
  (Polychromatic418967fa.accept_19_11_14_5_1_5629 11 90 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 90 119 (accept_3_2 10 90 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  90 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 90 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 90 119 (Polychromatic418967fa.accept_14_8_6_7_1_1934 8 90 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 119 (accept_3_2 7 90 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 90 119 (Polychromatic418967fa.accept_13_6_12_2_1_4707 6 90 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 90 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 90
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 90 119 (accept_3_2 4 90 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 90 119 (Polychromatic418967fa.accept_13_3_12_2_1_385 3
  90 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 119
  (Polychromatic418967fa.accept_19_2_14_5_1_5715 2 90 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 90 119 (accept_3_2 1 90 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  119)))))))))))))))))))))))))))))) (allB_succ' 31 89 119 (Eq.refl Bool.true) (allA_succ_of_accept 30 89 119
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 89 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 89 119 (Polychromatic418967fa.accept_13_3_11_2_1_1422 29 89 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 89 119 (accept_3_2 28 89 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 89 119 (Polychromatic418967fa.accept_19_8_13_5_1_1889 27 89 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 89 119
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 89 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 89 119 (accept_3_2 25 89 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  89 119 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 89 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 89 119 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 89 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 89 119 (accept_3_2 22 89 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 89 119 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 89 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 89 119
  (Polychromatic418967fa.accept_18_2_17_11_1_3178 20 89 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 89 119 (accept_3_2 19 89 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  89 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 89 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 89 119 (Polychromatic418967fa.accept_13_4_11_2_1_1458 17 89 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 89 119 (accept_3_2 16 89 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 89 119 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 89 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 89 119
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 89 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 89 119 (accept_3_2 13 89 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  89 119 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 89 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 89 119 (Polychromatic418967fa.accept_19_11_13_5_1_5714 11 89 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 89 119 (accept_3_2 10 89 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 89 119 (Polychromatic418967fa.accept_13_9_11_2_1_1491 9 89 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 89 119
  (Polychromatic418967fa.accept_16_8_9_7_1_768 8 89 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 89 119 (accept_3_2 7 89 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 89
  119 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 89 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 89 119 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 89 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 89 119 (accept_3_2 4 89 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 89 119 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 89 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 89 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 89
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 119 (accept_3_2 1 89 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 89 119))))))))))))))))))))))))))))))) (allB_succ' 32 88 119
  (Eq.refl Bool.true) (allA_of_3_0 32 88 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 87 119 (Eq.refl
  Bool.true) (allA_succ_of_accept 32 87 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 87 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 119 (accept_3_2 31 87 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 87 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 87 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 119
  (Polychromatic418967fa.accept_13_3_9_2_1_1486 29 87 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 87 119 (accept_3_2 28 87 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  87 119 (Polychromatic418967fa.accept_13_1_9_2_1_1448 27 87 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 87 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 87 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 119 (accept_3_2 25 87 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 87 119 (Polychromatic418967fa.accept_13_11_9_2_1_2969 24 87 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 119
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 87 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 87 119 (accept_3_2 22 87 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  87 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 87 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 87 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 87 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 119 (accept_3_2 19 87 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 87 119 (Polychromatic418967fa.accept_10_8_7_9_1_425 18 87 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 119
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 87 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 87 119 (accept_3_2 16 87 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  87 119 (Polychromatic418967fa.accept_19_15_11_5_1_5713 15 87 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 87 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 87 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 119 (accept_3_2 13 87 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 87 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 87 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 119
  (Polychromatic418967fa.accept_13_11_9_2_1_2969 11 87 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 119 (accept_3_2 10 87 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  87 119 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 87 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 87 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 87 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 119 (accept_3_2 7 87 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 87 119 (Polychromatic418967fa.accept_13_6_9_2_1_838 6 87 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 119
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 87 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 87 119 (accept_3_2 4 87 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87
  119 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 87 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 87 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 87 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 119 (accept_3_2 1 87 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 87 119))))))))))))))))))))))))))))))))) (allB_succ' 34 86 119 (Eq.refl Bool.true)
  (allA_succ_of_accept 33 86 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 86 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 119 (Polychromatic418967fa.accept_12_8_2_11_1_246 32 86 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 86 119 (accept_3_2 31 86 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 86 119 (Polychromatic418967fa.accept_9_3_5_2_1_28 30
  86 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 86 119
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 86 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 86 119 (accept_3_2 28 86 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  86 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 86 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 86 119 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 86 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 86 119 (accept_3_2 25 86 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 86 119 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 86 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 86 119
  (Polychromatic418967fa.accept_10_3_6_9_1_779 23 86 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 86 119 (accept_3_2 22 86 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  86 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 86 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 86 119 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 86 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 86 119 (accept_3_2 19 86 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 86 119 (Polychromatic418967fa.accept_15_3_11_14_1_1705 18 86 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 86 119
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 86 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 86 119 (accept_3_2 16 86 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  86 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 86 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 86 119 (Polychromatic418967fa.accept_19_14_10_5_1_3073 14 86 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 86 119 (accept_3_2 13 86 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 86 119 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 86 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 86 119
  (Polychromatic418967fa.accept_19_11_10_5_1_5662 11 86 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 86 119 (accept_3_2 10 86 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  86 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 86 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 86 119 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 86 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 86 119 (accept_3_2 7 86 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 86 119 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 86 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 86 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 86
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 119 (accept_3_2 4 86 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 86 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 86
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 119
  (Polychromatic418967fa.accept_18_2_14_11_1_3139 2 86 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 86 119 (accept_3_2 1 86 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  119)))))))))))))))))))))))))))))))))) (allB_succ' 35 85 119 (Eq.refl Bool.true) (allA_of_3_0 35 85 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 84 119 (Eq.refl Bool.true) (allA_succ_of_gcd 35 84 119 7 5 12 17
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 84 119
  (accept_3_2 34 84 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 84 119
  (Polychromatic418967fa.accept_9_6_3_2_1_431 33 84 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 84 119 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 84 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 119 (accept_3_2 31 84 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 84 119 (Polychromatic418967fa.accept_13_4_6_2_1_1437 30 84 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 84 119 (Polychromatic418967fa.accept_16_13_4_7_1_1537
  29 84 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 84 119 7 4 12 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 84 119
  (Polychromatic418967fa.accept_8_3_4_7_1_475 27 84 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 84 119 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 84 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 119 (accept_3_2 25 84 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 84 119 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 84 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 84 119 (Polychromatic418967fa.accept_9_5_3_2_1_171 23
  84 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 84 119 (accept_3_2 22 84
  119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 84 119 7 3 12 17 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 84 119
  (Polychromatic418967fa.accept_15_5_9_14_1_1724 20 84 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 84 119 (accept_3_2 19 84 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  84 119 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 84 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 84 119 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 84 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 84 119 (accept_3_2 16 84 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 84 119 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 84 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 119 7 2 12 17 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 119 (accept_3_2 13 84 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 119 (Polychromatic418967fa.accept_13_12_6_2_1_1441 12 84
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 84 119
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 84 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 84 119 (accept_3_2 10 84 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  84 119 (Polychromatic418967fa.accept_13_9_6_2_1_2200 9 84 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 84 119 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 84 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 84 119 7 1 12 17 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 84 119 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 84
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 84 119
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 84 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 84 119 (accept_3_2 4 84 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 84
  119 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 84 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 84 119 (Polychromatic418967fa.accept_11_2_7_9_1_890 2 84 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 119 (accept_3_2 1 84 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 84 119)))))))))))))))))))))))))))))))))))) (allB_succ' 37 83 119 (Eq.refl Bool.true)
  (allA_succ_of_accept 36 83 119 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 83 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 119 (Polychromatic418967fa.accept_13_9_5_2_1_2185 35 83 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 83 119 (accept_3_2 34 83 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 83 119 (Polychromatic418967fa.accept_13_7_5_2_1_401
  33 83 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 83 119
  (Polychromatic418967fa.accept_19_13_7_5_1_5712 32 83 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 83 119 (accept_3_2 31 83 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  83 119 (Polychromatic418967fa.accept_13_4_5_2_1_1436 30 83 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 83 119 (Polychromatic418967fa.accept_13_3_5_2_1_1475 29 83 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 83 119 (accept_3_2 28 83 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 83 119 (Polychromatic418967fa.accept_16_11_3_7_1_2375 27 83 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 83 119
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 26 83 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 83 119 (accept_3_2 25 83 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  83 119 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 83 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 83 119 (Polychromatic418967fa.accept_13_10_5_2_1_1477 23 83 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 83 119 (accept_3_2 22 83 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 83 119 (Polychromatic418967fa.accept_15_6_8_14_1_4575 21 83
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 83 119
  (Polychromatic418967fa.accept_8_4_3_7_1_491 20 83 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 83 119 (accept_3_2 19 83 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  83 119 (Polychromatic418967fa.accept_21_18_20_14_1_5711 18 83 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 83 119 (Polychromatic418967fa.accept_13_4_5_2_1_1436 17 83 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 83 119 (accept_3_2 16 83 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 83 119 (Polychromatic418967fa.accept_14_1_13_7_1_1205 15 83 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 83 119
  (Polychromatic418967fa.accept_10_4_3_9_1_1262 14 83 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 83 119 (accept_3_2 13 83 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  83 119 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 83 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 83 119 (Polychromatic418967fa.accept_16_11_3_7_1_2375 11 83 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 83 119 (accept_3_2 10 83 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 83 119 (Polychromatic418967fa.accept_13_9_5_2_1_2185 9 83 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 83 119
  (Polychromatic418967fa.accept_14_8_13_7_1_2798 8 83 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 83 119 (accept_3_2 7 83 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 83
  119 (Polychromatic418967fa.accept_10_6_3_9_1_1207 6 83 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 83 119 (Polychromatic418967fa.accept_15_5_8_14_1_432 5 83 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 83 119 (accept_3_2 4 83 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 83 119 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 83 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 119
  (Polychromatic418967fa.accept_19_2_7_5_1_3067 2 83 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 83 119 (accept_3_2 1 83 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 83
  119))))))))))))))))))))))))))))))))))))) (allB_succ' 38 82 119 (Eq.refl Bool.true) (allA_of_3_0 38 82 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 81 119 (Eq.refl Bool.true) (allA_succ_of_accept 38 81 119
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 81 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 81 119 (accept_3_2 37 81 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  81 119 (Polychromatic418967fa.accept_13_10_3_2_1_4728 36 81 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 81 119 (Polychromatic418967fa.accept_10_5_1_9_1_791 35 81 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 119 (accept_3_2 34 81 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 119 (Polychromatic418967fa.accept_18_15_9_11_1_4371 33 81 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 81 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 81 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 81 119 (accept_3_2 31 81 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  81 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 81 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 81 119 (Polychromatic418967fa.accept_22_7_15_9_1_5710 29 81 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 119 (accept_3_2 28 81 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 119 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 81 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 81 119
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 81 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 81 119 (accept_3_2 25 81 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  81 119 (Polychromatic418967fa.accept_11_2_4_9_1_484 24 81 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 81 119 (Polychromatic418967fa.accept_13_10_3_2_1_4728 23 81 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 119 (accept_3_2 22 81 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 119 (Polychromatic418967fa.accept_25_21_6_19_1_5709 21 81
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 81 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 81 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 81 119 (accept_3_2 19 81 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  81 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 81 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 81 119 (Polychromatic418967fa.accept_14_3_11_7_1_1260 17 81 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 119 (accept_3_2 16 81 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 119 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 81 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 81 119
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 81 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 119 (accept_3_2 13 81 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  81 119 (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 81 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 81 119 (Polychromatic418967fa.accept_13_11_3_2_1_863 11 81 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 119 (accept_3_2 10 81 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 119 (Polychromatic418967fa.accept_13_9_3_2_1_399 9 81 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 81 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 81 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 81 119 (accept_3_2 7 81 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 81
  119 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 81 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 81 119 (Polychromatic418967fa.accept_10_5_1_9_1_791 5 81 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 119 (accept_3_2 4 81 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 81 119 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 81 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 81
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 119 (accept_3_2 1 81 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81 119))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 80 119
  (Eq.refl Bool.true) (allA_succ_of_accept 39 80 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 80 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 119
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 80 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 80 119 (accept_3_2 37 80 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  80 119 (Polychromatic418967fa.accept_15_6_5_14_1_429 36 80 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 80 119 (Polychromatic418967fa.accept_23_12_11_4_1_5708 35 80 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 80 119 (accept_3_2 34 80 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 80 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 80 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 80 119
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 80 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 80 119 (accept_3_2 31 80 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  80 119 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 80 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 80 119 (Polychromatic418967fa.accept_21_8_17_14_1_4156 29 80 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 119 (accept_3_2 28 80 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 80 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 119
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 80 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 80 119 (accept_3_2 25 80 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  80 119 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 80 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 80 119 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 80 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 119 (accept_3_2 22 80 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 80 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 80 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 80 119
  (Polychromatic418967fa.accept_19_1_4_5_1_4313 20 80 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 80 119 (accept_3_2 19 80 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  80 119 (Polychromatic418967fa.accept_14_4_10_7_1_1946 18 80 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 80 119 (Polychromatic418967fa.accept_11_6_3_9_1_906 17 80 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 119 (accept_3_2 16 80 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 80 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 80 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 80 119
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 80 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 80 119 (accept_3_2 13 80 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  80 119 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 80 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 80 119 (Polychromatic418967fa.accept_14_11_10_7_1_1948 11 80 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 80 119 (accept_3_2 10 80 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 80 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 80 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 119
  (Polychromatic418967fa.accept_15_8_5_14_1_986 8 80 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 80 119 (accept_3_2 7 80 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80
  119 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 80 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 80 119 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 80 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 80 119 (accept_3_2 4 80 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 80 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 80 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 119 (Polychromatic418967fa.accept_12_2_8_11_1_31 2
  80 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 80 119 (accept_3_2 1 80 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80 119)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 79
  119 (Eq.refl Bool.true) (allA_of_3_0 41 79 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 78 119 (Eq.refl
  Bool.true) (allA_succ_of_accept 41 78 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 78 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 78 119 (accept_3_2 40 78 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 78 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 78 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 78 119
  (Polychromatic418967fa.accept_21_17_15_14_1_5707 38 78 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 78 119 (accept_3_2 37 78 119 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 78 119 (Polychromatic418967fa.accept_16_4_14_7_1_5641 36 78 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 78 119 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 78 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 78 119 (accept_3_2 34 78 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 78 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 33
  78 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 78 119
  (Polychromatic418967fa.accept_9_5_6_2_1_161 32 78 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 78 119 (accept_3_2 31 78 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  78 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 78 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 78 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 78 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 78 119 (accept_3_2 28 78 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 78 119 (Polychromatic418967fa.accept_10_7_8_9_1_785 27 78 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 78 119
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 78 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 78 119 (accept_3_2 25 78 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  78 119 (Polychromatic418967fa.accept_10_4_8_9_1_784 24 78 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 78 119 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 78 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 78 119 (accept_3_2 22 78 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 78 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 78 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 78 119
  (Polychromatic418967fa.accept_14_6_8_7_1_589 20 78 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 78 119 (accept_3_2 19 78 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  78 119 (Polychromatic418967fa.accept_19_18_2_5_1_5682 18 78 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 78 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 78 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 78 119 (accept_3_2 16 78 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 78 119 (Polychromatic418967fa.accept_14_1_8_7_1_1253 15 78 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 78 119
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 78 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 78 119 (accept_3_2 13 78 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  78 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 78 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 78 119 (Polychromatic418967fa.accept_10_1_8_9_1_787 11 78 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 78 119 (accept_3_2 10 78 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 78 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 78 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 78 119
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 78 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 78 119 (accept_3_2 7 78 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 78
  119 (Polychromatic418967fa.accept_14_6_8_7_1_589 6 78 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 78 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 78 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78 119 (accept_3_2 4 78 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 78 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 78 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 119 (Polychromatic418967fa.accept_15_2_3_14_1_972 2
  78 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 78 119 (accept_3_2 1 78 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78 119)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 77
  119 (Eq.refl Bool.true) (allA_succ_of_gcd 42 77 119 7 6 11 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 77 119 (Polychromatic418967fa.accept_16_9_13_7_1_1509 41 77 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 77 119 (accept_3_2 40 77 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 77 119 (Polychromatic418967fa.accept_9_3_5_2_1_28 39
  77 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 77 119
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 77 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 77 119 (accept_3_2 37 77 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  77 119 (Polychromatic418967fa.accept_13_10_12_2_1_1460 36 77 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 77 119 7 5 11 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 77 119 (accept_3_2 34 77 119 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 77 119 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 77 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 77 119 (Polychromatic418967fa.accept_10_2_7_9_1_783 32 77 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 119 (accept_3_2 31 77 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 30
  77 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 119
  (Polychromatic418967fa.accept_13_3_12_2_1_385 29 77 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 77 119 7 4 11 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 77 119 (Polychromatic418967fa.accept_13_1_12_2_1_384 27 77 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 77 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 77 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 119 (accept_3_2 25 77 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 119 (Polychromatic418967fa.accept_9_6_5_2_1_421 24
  77 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 119
  (Polychromatic418967fa.accept_13_10_12_2_1_1460 23 77 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 119 (accept_3_2 22 77 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 77
  119 7 3 11 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20
  77 119 (Polychromatic418967fa.accept_15_5_2_14_1_1693 20 77 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 77 119 (accept_3_2 19 77 119 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 77 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 77 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 119 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 77 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 77 119 (accept_3_2 16 77 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 77 119 (Polychromatic418967fa.accept_9_6_5_2_1_421 15
  77 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 77 119 7 2 11 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 77 119 (accept_3_2 13
  77 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 119
  (Polychromatic418967fa.accept_9_3_5_2_1_28 12 77 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 77 119 (Polychromatic418967fa.accept_24_11_5_23_1_5706 11 77 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 77 119 (accept_3_2 10 77 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 77 119 (Polychromatic418967fa.accept_16_9_13_7_1_1509 9 77 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 77 119 (Polychromatic418967fa.accept_9_8_5_2_1_422 8
  77 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 77 119 7 1 11 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 77 119
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 77 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 77 119 (Polychromatic418967fa.accept_13_5_12_2_1_1423 5 77 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 77 119 (accept_3_2 4 77 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 77 119 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 77 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 77 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 77
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 119 (accept_3_2 1 77 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 77 119))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 76
  119 (Eq.refl Bool.true) (allA_of_3_0 44 76 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 75 119 (Eq.refl
  Bool.true) (allA_succ_of_accept 44 75 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 75 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 119 (accept_3_2 43 75 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 75 119 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 75 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 119
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 75 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 75 119 (accept_3_2 40 75 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  75 119 (Polychromatic418967fa.accept_19_1_18_5_1_5705 39 75 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 75 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 75 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 119 (accept_3_2 37 75 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 75 119 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 75 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 75 119
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 75 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 75 119 (accept_3_2 34 75 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  75 119 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 75 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 75 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 75 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 119 (accept_3_2 31 75 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 75 119 (Polychromatic418967fa.accept_14_2_5_7_1_3767 30 75 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 75 119
  (Polychromatic418967fa.accept_13_3_10_2_1_381 29 75 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 75 119 (accept_3_2 28 75 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  75 119 (Polychromatic418967fa.accept_21_6_12_14_1_5704 27 75 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 75 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 75 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 119 (accept_3_2 25 75 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 75 119 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 75 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 75 119
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 75 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 75 119 (accept_3_2 22 75 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  75 119 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 75 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 75 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 75 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 119 (accept_3_2 19 75 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 119 (Polychromatic418967fa.accept_13_5_10_2_1_856 18 75 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 119
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 75 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 75 119 (accept_3_2 16 75 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  75 119 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 75 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 75 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 75 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 119 (accept_3_2 13 75 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 75 119 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 75 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 119
  (Polychromatic418967fa.accept_10_1_5_9_1_157 11 75 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 75 119 (accept_3_2 10 75 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  75 119 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 75 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 75 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 75 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 119 (accept_3_2 7 75 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 119 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 75 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 75 119
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 75 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 75 119 (accept_3_2 4 75 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75
  119 (Polychromatic418967fa.accept_13_3_10_2_1_381 3 75 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 75 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 75 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 119 (accept_3_2 1 75 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 75 119))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 74 119 (Eq.refl
  Bool.true) (allA_succ_of_accept 45 74 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 74 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 119 (Polychromatic418967fa.accept_12_8_2_11_1_246
  44 74 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 74 119 (accept_3_2 43
  74 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 74 119
  (Polychromatic418967fa.accept_13_3_9_2_1_1486 42 74 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 74 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 74 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 119 (accept_3_2 40 74 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 74 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 74 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 119 (Polychromatic418967fa.accept_10_8_4_9_1_1229
  38 74 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 74 119 (accept_3_2 37
  74 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 74 119
  (Polychromatic418967fa.accept_27_9_20_11_1_5703 36 74 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 74 119 (Polychromatic418967fa.accept_10_5_4_9_1_420 35 74 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 119 (accept_3_2 34 74 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 74 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 74 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 119 (Polychromatic418967fa.accept_11_10_8_9_1_492
  32 74 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 74 119 (accept_3_2 31
  74 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 74 119
  (Polychromatic418967fa.accept_16_14_10_7_1_2363 30 74 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 74 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 74 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 119 (accept_3_2 28 74 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 74 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 74 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 119 (Polychromatic418967fa.accept_19_7_17_5_1_3081
  26 74 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 74 119 (accept_3_2 25
  74 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 74 119
  (Polychromatic418967fa.accept_13_11_9_2_1_2969 24 74 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 74 119 (Polychromatic418967fa.accept_10_3_4_9_1_15 23 74 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 119 (accept_3_2 22 74 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 74 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 74 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 119 (Polychromatic418967fa.accept_12_8_2_11_1_246
  20 74 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 74 119 (accept_3_2 19
  74 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 74 119
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 74 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 74 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 74 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 119 (accept_3_2 16 74 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 74 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 74 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 119 (Polychromatic418967fa.accept_13_1_9_2_1_1448
  14 74 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 74 119 (accept_3_2 13
  74 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 74 119
  (Polychromatic418967fa.accept_19_12_17_5_1_5702 12 74 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 74 119 (Polychromatic418967fa.accept_13_11_9_2_1_2969 11 74 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 119 (accept_3_2 10 74 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 74 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 74 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 119 (Polychromatic418967fa.accept_10_8_4_9_1_1229 8
  74 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 74 119 (accept_3_2 7 74 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74 119 (Polychromatic418967fa.accept_13_6_9_2_1_838 6
  74 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 74 119
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 74 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 74 119 (accept_3_2 4 74 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 74
  119 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 74 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 74 119 (Polychromatic418967fa.accept_19_2_17_5_1_5643 2 74 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 119 (accept_3_2 1 74 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 74 119)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 73 119 (Eq.refl Bool.true)
  (allA_of_3_0 47 73 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 72 119 (Eq.refl Bool.true)
  (allA_succ_of_accept 47 72 119 (Polychromatic418967fa.accept_10_7_2_9_1_775 47 72 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 72 119 (accept_3_2 46 72 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 72 119 (Polychromatic418967fa.accept_21_3_9_14_1_5701 45 72 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 72 119
  (Polychromatic418967fa.accept_13_5_7_2_1_852 44 72 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 72 119 (accept_3_2 43 72 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  72 119 (Polychromatic418967fa.accept_19_4_15_5_1_3043 42 72 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 72 119 (Polychromatic418967fa.accept_10_1_2_9_1_152 41 72 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 72 119 (accept_3_2 40 72 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 72 119 (Polychromatic418967fa.accept_15_9_12_14_1_963 39 72 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 72 119
  (Polychromatic418967fa.accept_21_17_9_14_1_5700 38 72 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 72 119 (accept_3_2 37 72 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  72 119 (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 72 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 72 119 (Polychromatic418967fa.accept_13_9_7_2_1_3869 35 72 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 72 119 (accept_3_2 34 72 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 72 119 (Polychromatic418967fa.accept_14_5_2_7_1_2804 33 72 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 72 119
  (Polychromatic418967fa.accept_15_2_12_14_1_1709 32 72 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 72 119 (accept_3_2 31 72 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  72 119 (Polychromatic418967fa.accept_19_11_15_5_1_5699 30 72 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 72 119 (Polychromatic418967fa.accept_19_10_15_5_1_5698 29 72 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 72 119 (accept_3_2 28 72 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 72 119 (Polychromatic418967fa.accept_10_7_2_9_1_775 27 72 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 72 119
  (Polychromatic418967fa.accept_14_12_2_7_1_1243 26 72 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 72 119 (accept_3_2 25 72 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  72 119 (Polychromatic418967fa.accept_15_9_12_14_1_963 24 72 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 72 119 (Polychromatic418967fa.accept_14_9_2_7_1_1242 23 72 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 72 119 (accept_3_2 22 72 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 72 119 (Polychromatic418967fa.accept_10_1_2_9_1_152 21 72 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 72 119
  (Polychromatic418967fa.accept_16_4_8_7_1_3396 20 72 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 72 119 (accept_3_2 19 72 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  72 119 (Polychromatic418967fa.accept_13_5_7_2_1_852 18 72 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 72 119 (Polychromatic418967fa.accept_10_7_2_9_1_775 17 72 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 72 119 (accept_3_2 16 72 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 72 119 (Polychromatic418967fa.accept_16_15_8_7_1_3407 15 72 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 72 119
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 14 72 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 72 119 (accept_3_2 13 72 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  72 119 (Polychromatic418967fa.accept_14_12_2_7_1_1243 12 72 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 72 119 (Polychromatic418967fa.accept_10_1_2_9_1_152 11 72 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 72 119 (accept_3_2 10 72 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 72 119 (Polychromatic418967fa.accept_13_9_7_2_1_3869 9 72 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 72 119
  (Polychromatic418967fa.accept_13_8_7_2_1_2988 8 72 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 72 119 (accept_3_2 7 72 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 72
  119 (Polychromatic418967fa.accept_19_6_15_5_1_5697 6 72 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 72 119 (Polychromatic418967fa.accept_13_5_7_2_1_852 5 72 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 72 119 (accept_3_2 4 72 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 72 119 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 72 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 72 119
  (Polychromatic418967fa.accept_15_2_12_14_1_1709 2 72 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 72 119 (accept_3_2 1 72 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  119)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 71 119 (Eq.refl Bool.true) (allA_succ_of_accept 48
  71 119 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 71 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 71 119 (Polychromatic418967fa.accept_13_8_6_2_1_865 47 71 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 71 119 (accept_3_2 46 71 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 71 119 (Polychromatic418967fa.accept_10_5_1_9_1_791 45 71 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 71 119
  (Polychromatic418967fa.accept_19_6_14_5_1_4339 44 71 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 71 119 (accept_3_2 43 71 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  71 119 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 71 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 71 119 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 71 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 71 119 (accept_3_2 40 71 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 71 119 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 71 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 71 119
  (Polychromatic418967fa.accept_10_8_1_9_1_413 38 71 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 71 119 (accept_3_2 37 71 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  71 119 (Polychromatic418967fa.accept_13_10_6_2_1_1440 36 71 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 71 119 (Polychromatic418967fa.accept_10_5_1_9_1_791 35 71 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 71 119 (accept_3_2 34 71 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 71 119 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 71 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 71 119
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 71 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 71 119 (accept_3_2 31 71 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  71 119 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 71 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 71 119 (Polychromatic418967fa.accept_11_7_5_9_1_884 29 71 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 71 119 (accept_3_2 28 71 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 71 119 (Polychromatic418967fa.accept_13_1_6_2_1_377 27 71 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 71 119
  (Polychromatic418967fa.accept_21_5_8_14_1_5696 26 71 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 71 119 (accept_3_2 25 71 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  71 119 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 71 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 71 119 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 71 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 71 119 (accept_3_2 22 71 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 71 119 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 71 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 71 119
  (Polychromatic418967fa.accept_14_6_1_7_1_2775 20 71 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 71 119 (accept_3_2 19 71 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  71 119 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 71 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 71 119 (Polychromatic418967fa.accept_13_4_6_2_1_1437 17 71 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 71 119 (accept_3_2 16 71 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 71 119 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 71 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 71 119
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 71 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 71 119 (accept_3_2 13 71 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  71 119 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 71 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 71 119 (Polychromatic418967fa.accept_19_11_14_5_1_5629 11 71 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 71 119 (accept_3_2 10 71 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 71 119 (Polychromatic418967fa.accept_13_9_6_2_1_2200 9 71 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 119
  (Polychromatic418967fa.accept_10_8_1_9_1_413 8 71 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 71 119 (accept_3_2 7 71 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71
  119 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 71 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 71 119 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 71 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 71 119 (accept_3_2 4 71 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 71 119 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 71 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 119 (Polychromatic418967fa.accept_10_2_1_9_1_1248 2
  71 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 119 (accept_3_2 1 71 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 71 119))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  50 70 119 (Eq.refl Bool.true) (allA_of_3_0 50 70 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 69 119
  (Eq.refl Bool.true) (allA_succ_of_accept 50 69 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 69 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 119 (accept_3_2 49 69 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 69 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 69 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 119
  (Polychromatic418967fa.accept_19_9_12_5_1_5695 47 69 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 69 119 (accept_3_2 46 69 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  69 119 (Polychromatic418967fa.accept_13_6_4_2_1_1433 45 69 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 69 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 69 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 119 (accept_3_2 43 69 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 69 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 69 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 119
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 69 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 69 119 (accept_3_2 40 69 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  69 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 69 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 69 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 69 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 119 (accept_3_2 37 69 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 69 119 (Polychromatic418967fa.accept_14_8_13_7_1_2798 36 69 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 119
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 69 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 69 119 (accept_3_2 34 69 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  69 119 (Polychromatic418967fa.accept_20_13_9_19_1_5694 33 69 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 69 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 69 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 119 (accept_3_2 31 69 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 69 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 69 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 119
  (Polychromatic418967fa.accept_14_1_13_7_1_1205 29 69 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 69 119 (accept_3_2 28 69 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  69 119 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 69 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 69 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 69 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 119 (accept_3_2 25 69 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 69 119 (Polychromatic418967fa.accept_13_11_4_2_1_2954 24 69 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 119
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 69 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 69 119 (accept_3_2 22 69 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  69 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 69 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 69 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 69 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 119 (accept_3_2 19 69 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 69 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 69 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 119
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 69 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 69 119 (accept_3_2 16 69 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  69 119 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 69 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 69 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 69 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 119 (accept_3_2 13 69 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 69 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 69 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 119
  (Polychromatic418967fa.accept_13_11_4_2_1_2954 11 69 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 119 (accept_3_2 10 69 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  69 119 (Polychromatic418967fa.accept_18_9_15_11_1_5693 9 69 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 69 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 69 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 119 (accept_3_2 7 69 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 69 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 69 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 119
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 69 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 69 119 (accept_3_2 4 69 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69
  119 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 69 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 69 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 69 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 119 (accept_3_2 1 69 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 69 119))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 68 119 (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 68 119 17 3 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 68 119 (Polychromatic418967fa.accept_12_2_8_11_1_31 50 68 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 68 119 (accept_3_2 49 68 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 68 119 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 68 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 68 119
  (Polychromatic418967fa.accept_10_7_8_9_1_785 47 68 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 68 119 (accept_3_2 46 68 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  68 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 68 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 68 119 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 68 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 68 119 (accept_3_2 43 68 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 68 119 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 68 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 68 119
  (Polychromatic418967fa.accept_10_1_8_9_1_787 41 68 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 68 119 (accept_3_2 40 68 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  68 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 68 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 68 119 (Polychromatic418967fa.accept_12_2_8_11_1_31 38 68 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 68 119 (accept_3_2 37 68 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 68 119 (Polychromatic418967fa.accept_13_10_3_2_1_4728 36 68 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 68 119
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 68 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 68 119 17 2 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 68 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 68 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 119 (Polychromatic418967fa.accept_19_13_11_5_1_5692 32 68
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 68 119 (accept_3_2 31 68 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 68 119 (Polychromatic418967fa.accept_9_3_5_2_1_28 30
  68 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 68 119
  (Polychromatic418967fa.accept_11_7_2_9_1_480 29 68 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 68 119 (accept_3_2 28 68 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  68 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 68 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 68 119 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 68 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 68 119 (accept_3_2 25 68 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 68 119 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 68 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 68 119
  (Polychromatic418967fa.accept_13_10_3_2_1_4728 23 68 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 68 119 (accept_3_2 22 68 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  68 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 68 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 68 119 (Polychromatic418967fa.accept_15_5_8_14_1_432 20 68 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 68 119 (accept_3_2 19 68 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 68 119 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 68 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 17 68 119 17 1 4 7 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 16 68 119 (accept_3_2 16 68 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 68 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 68 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 119
  (Polychromatic418967fa.accept_10_4_8_9_1_784 14 68 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 68 119 (accept_3_2 13 68 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  68 119 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 68 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 68 119 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 68 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 119 (accept_3_2 10 68 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 68 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 68 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 119
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 68 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 68 119 (accept_3_2 7 68 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68
  119 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 68 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 68 119 (Polychromatic418967fa.accept_13_5_3_2_1_1499 5 68 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 119 (accept_3_2 4 68 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 68 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 68 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 119 (Polychromatic418967fa.accept_12_2_8_11_1_31 2
  68 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 119 (accept_3_2 1 68 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68 119))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 53 67 119 (Eq.refl Bool.true) (allA_of_3_0 53 67 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  54 66 119 (Eq.refl Bool.true) (allA_succ_of_accept 53 66 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 66 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 66 119 (accept_3_2 52 66 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 66 119 (Polychromatic418967fa.accept_9_6_3_2_1_431 51
  66 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 66 119
  (Polychromatic418967fa.accept_9_5_3_2_1_171 50 66 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 66 119 (accept_3_2 49 66 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  66 119 (Polychromatic418967fa.accept_13_9_1_2_1_2952 48 66 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 66 119 (Polychromatic418967fa.accept_20_7_6_19_1_2949 47 66 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 66 119 (accept_3_2 46 66 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 66 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 66 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 66 119
  (Polychromatic418967fa.accept_9_8_3_2_1_417 44 66 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 66 119 (accept_3_2 43 66 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  66 119 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 66 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 66 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 66 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 119 (accept_3_2 40 66 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 66 119 (Polychromatic418967fa.accept_14_11_10_7_1_1948 39 66 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 66 119
  (Polychromatic418967fa.accept_13_12_1_2_1_845 38 66 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 66 119 (accept_3_2 37 66 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  66 119 (Polychromatic418967fa.accept_21_15_3_14_1_4141 36 66 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 66 119 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 66 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 66 119 (accept_3_2 34 66 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 66 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 66 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 66 119
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 66 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 66 119 (accept_3_2 31 66 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  66 119 (Polychromatic418967fa.accept_20_10_6_19_1_5691 30 66 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 66 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 66 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 66 119 (accept_3_2 28 66 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 66 119 (Polychromatic418967fa.accept_16_11_2_7_1_3374 27 66 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 66 119
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 66 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 66 119 (accept_3_2 25 66 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  66 119 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 66 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 66 119 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 66 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 66 119 (accept_3_2 22 66 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 66 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 66 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 66 119
  (Polychromatic418967fa.accept_15_5_6_14_1_1721 20 66 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 66 119 (accept_3_2 19 66 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  66 119 (Polychromatic418967fa.accept_14_4_10_7_1_1946 18 66 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 66 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 66 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 66 119 (accept_3_2 16 66 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 66 119 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 66 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 66 119
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 66 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 66 119 (accept_3_2 13 66 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  66 119 (Polychromatic418967fa.accept_13_12_1_2_1_845 12 66 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 66 119 (Polychromatic418967fa.accept_14_11_10_7_1_1948 11 66 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 66 119 (accept_3_2 10 66 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 66 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 66 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 66 119
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 66 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 66 119 (accept_3_2 7 66 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 66
  119 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 66 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 66 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 66 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66 119 (accept_3_2 4 66 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 66 119 (Polychromatic418967fa.accept_10_3_6_9_1_779 3 66 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 119 (Polychromatic418967fa.accept_21_2_3_14_1_5690
  2 66 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 119 (accept_3_2 1 66
  119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66 119))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 55 65 119 (Eq.refl Bool.true) (allA_succ_of_accept 54 65 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 54
  65 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 119
  (Polychromatic418967fa.accept_15_8_5_14_1_986 53 65 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 65 119 (accept_3_2 52 65 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  65 119 (Polychromatic418967fa.accept_10_1_5_9_1_157 51 65 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 65 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 65 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 119 (accept_3_2 49 65 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 119 (Polychromatic418967fa.accept_19_10_8_5_1_5689 48 65 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 119
  (Polychromatic418967fa.accept_14_5_9_7_1_590 47 65 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 119 (accept_3_2 46 65 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 119 (Polychromatic418967fa.accept_11_1_10_9_1_871 45 65 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 119 (Polychromatic418967fa.accept_10_4_5_9_1_1231 44 65 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 119 (accept_3_2 43 65 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 65 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 119
  (Polychromatic418967fa.accept_10_1_5_9_1_157 41 65 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 119 (accept_3_2 40 65 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 119 (Polychromatic418967fa.accept_15_9_5_14_1_973 39 65 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 65 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 119 (accept_3_2 37 65 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 119 (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 65 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 119
  (Polychromatic418967fa.accept_19_16_8_5_1_4322 35 65 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 119 (accept_3_2 34 65 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 119 (Polychromatic418967fa.accept_14_5_9_7_1_590 33 65 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 119 (Polychromatic418967fa.accept_15_2_5_14_1_61 32 65 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 119 (accept_3_2 31 65 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 65 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 119
  (Polychromatic418967fa.accept_19_10_8_5_1_5689 29 65 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 119 (accept_3_2 28 65 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 119 (Polychromatic418967fa.accept_21_6_2_14_1_5688 27 65 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 65 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 119 (accept_3_2 25 65 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 119 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 65 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 119
  (Polychromatic418967fa.accept_11_1_10_9_1_871 23 65 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 119 (accept_3_2 22 65 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 119 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 65 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 119 (Polychromatic418967fa.accept_21_20_2_14_1_5687 20 65 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 119 (accept_3_2 19 65 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 65 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 119
  (Polychromatic418967fa.accept_15_2_5_14_1_61 17 65 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 119 (accept_3_2 16 65 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 119 (Polychromatic418967fa.accept_20_15_5_19_1_5686 15 65 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 65 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 119 (accept_3_2 13 65 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 119 (Polychromatic418967fa.accept_11_1_10_9_1_871 12 65 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 119
  (Polychromatic418967fa.accept_10_1_5_9_1_157 11 65 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 119 (accept_3_2 10 65 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 119 (Polychromatic418967fa.accept_15_9_5_14_1_973 9 65 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 119 (Polychromatic418967fa.accept_11_8_10_9_1_1401 8 65 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 119 (accept_3_2 7 65 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 65 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 119
  (Polychromatic418967fa.accept_14_5_9_7_1_590 5 65 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 119 (accept_3_2 4 65 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  119 (Polychromatic418967fa.accept_19_3_8_5_1_1875 3 65 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 65 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 65 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 119 (accept_3_2 1 65 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 65 119))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 64 119
  (Eq.refl Bool.true) (allA_of_3_0 56 64 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 63 119 (Eq.refl
  Bool.true) (allA_succ_of_gcd 56 63 119 7 8 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 63 119 (accept_3_2 55 63 119 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 63 119 (Polychromatic418967fa.accept_10_4_3_9_1_1262 54 63 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 119 (Polychromatic418967fa.accept_19_15_6_5_1_4356 53 63
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 119 (accept_3_2 52 63 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 119 (Polychromatic418967fa.accept_16_3_15_7_1_3417
  51 63 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 63 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 49 63 119 7 7 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 48 63 119 (Polychromatic418967fa.accept_13_9_11_2_1_1491 48 63 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 119 (Polychromatic418967fa.accept_15_2_3_14_1_972 47 63 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 119 (accept_3_2 46 63 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 119 (Polychromatic418967fa.accept_12_9_3_11_1_1097
  45 63 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 63 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 119 (accept_3_2 43 63 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 63
  119 7 6 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  63 119 (Polychromatic418967fa.accept_15_11_3_14_1_971 41 63 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 63 119 (accept_3_2 40 63 119 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 63 119 (Polychromatic418967fa.accept_19_1_6_5_1_4319 39 63 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 63 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 119 (accept_3_2 37 63 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 63 119 (Polychromatic418967fa.accept_10_6_3_9_1_1207
  36 63 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 63 119 7 5 9 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 63 119 (accept_3_2 34
  63 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 119
  (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 63 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 63 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 63 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 119 (accept_3_2 31 63 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 63 119 (Polychromatic418967fa.accept_13_4_11_2_1_1458 30 63 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 119
  (Polychromatic418967fa.accept_13_3_11_2_1_1422 29 63 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 63 119 7 4 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 63 119 (Polychromatic418967fa.accept_16_11_15_7_1_5654 27 63 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 63 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 119 (accept_3_2 25 63 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 63 119 (Polychromatic418967fa.accept_10_4_3_9_1_1262
  24 63 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 119
  (Polychromatic418967fa.accept_13_10_11_2_1_3862 23 63 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 63 119 (accept_3_2 22 63 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63
  119 7 3 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20
  63 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 63 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 63 119 (accept_3_2 19 63 119 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 63 119 (Polychromatic418967fa.accept_19_18_6_5_1_4321 18 63 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 119 (Polychromatic418967fa.accept_13_4_11_2_1_1458 17 63
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 119 (accept_3_2 16 63 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 119
  (Polychromatic418967fa.accept_18_15_9_11_1_4371 15 63 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 63 119 7 2 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 63 119 (accept_3_2 13 63 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 119 (Polychromatic418967fa.accept_18_12_9_11_1_4370 12 63 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 119 (Polychromatic418967fa.accept_15_11_3_14_1_971 11 63 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 119 (accept_3_2 10 63 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 119 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 63 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 63 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 63 119 7 1 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 63 119 (Polychromatic418967fa.accept_10_6_3_9_1_1207 6 63 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 119 (Polychromatic418967fa.accept_24_5_15_23_1_5647 5 63 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 119 (accept_3_2 4 63 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 119 (Polychromatic418967fa.accept_13_3_11_2_1_1422
  3 63 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 63 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 63 119 (accept_3_2 1 63 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  119))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 62 119 (Eq.refl Bool.true)
  (allA_succ_of_accept 57 62 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 62 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 119 (Polychromatic418967fa.accept_12_8_2_11_1_246 56 62 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 62 119 (accept_3_2 55 62 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 62 119
  (Polychromatic418967fa.accept_22_10_18_9_1_5685 54 62 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 62 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 62 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 119 (accept_3_2 52 62 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 62 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 62 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 119 (Polychromatic418967fa.accept_9_5_8_2_1_409 50
  62 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 62 119 (accept_3_2 49 62
  119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 62 119
  (Polychromatic418967fa.accept_9_3_8_2_1_162 48 62 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 62 119 (Polychromatic418967fa.accept_10_7_2_9_1_775 47 62 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 119 (accept_3_2 46 62 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 62 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 62 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 119 (Polychromatic418967fa.accept_12_8_2_11_1_246
  44 62 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 62 119 (accept_3_2 43
  62 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 62 119
  (Polychromatic418967fa.accept_9_6_8_2_1_410 42 62 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 62 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 62 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 119 (accept_3_2 40 62 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 62 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 62 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 119 (Polychromatic418967fa.accept_11_5_7_9_1_2696
  38 62 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 62 119 (accept_3_2 37
  62 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 62 119
  (Polychromatic418967fa.accept_14_8_6_7_1_1934 36 62 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 62 119 (Polychromatic418967fa.accept_11_2_7_9_1_890 35 62 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 62 119 (accept_3_2 34 62 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 62 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 62 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 62 119 (Polychromatic418967fa.accept_9_5_8_2_1_409 32
  62 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 62 119 (accept_3_2 31 62
  119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 62 119
  (Polychromatic418967fa.accept_9_3_8_2_1_162 30 62 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 62 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 62 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 62 119 (accept_3_2 28 62 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 62 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 62 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 62 119
  (Polychromatic418967fa.accept_16_10_14_7_1_2372 26 62 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 62 119 (accept_3_2 25 62 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  62 119 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 62 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 62 119 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 62 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 62 119 (accept_3_2 22 62 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 62 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 62 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 62 119
  (Polychromatic418967fa.accept_12_8_2_11_1_246 20 62 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 62 119 (accept_3_2 19 62 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  62 119 (Polychromatic418967fa.accept_13_5_10_2_1_856 18 62 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 62 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 62 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 62 119 (accept_3_2 16 62 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 62 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 62 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 62 119
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 62 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 62 119 (accept_3_2 13 62 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  62 119 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 62 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 62 119 (Polychromatic418967fa.accept_10_1_2_9_1_152 11 62 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 62 119 (accept_3_2 10 62 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 62 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 62 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 62 119
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 62 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 62 119 (accept_3_2 7 62 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 62
  119 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 62 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 62 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 62 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 119 (accept_3_2 4 62 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 62 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 62 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 119 (Polychromatic418967fa.accept_11_2_7_9_1_890 2
  62 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 119 (accept_3_2 1 62 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62 119))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 59 61 119 (Eq.refl Bool.true) (allA_of_3_0 59 61 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ
  60 119 (allA_succ_of_accept 59 60 119 (Polychromatic418967fa.accept_8_3_4_7_1_475 59 60 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 60 119 (accept_3_2 58 60 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 60 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 60 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 60 119
  (Polychromatic418967fa.accept_16_8_12_7_1_2399 56 60 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 60 119 (accept_3_2 55 60 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  60 119 (Polychromatic418967fa.accept_19_16_3_5_1_5684 54 60 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 60 119 (Polychromatic418967fa.accept_9_8_6_2_1_744 53 60 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 60 119 (accept_3_2 52 60 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 60 119 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 60 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 60 119
  (Polychromatic418967fa.accept_9_5_6_2_1_161 50 60 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 60 119 (accept_3_2 49 60 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  60 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 60 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 60 119 (Polychromatic418967fa.accept_21_5_18_14_1_2793 47 60 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 60 119 (accept_3_2 46 60 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 60 119 (Polychromatic418967fa.accept_13_6_8_2_1_1484 45 60 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 60 119
  (Polychromatic418967fa.accept_9_8_6_2_1_744 44 60 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 60 119 (accept_3_2 43 60 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  60 119 (Polychromatic418967fa.accept_23_19_14_4_1_5683 42 60 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 60 119 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 60 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 60 119 (accept_3_2 40 60 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 60 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 60 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 60 119
  (Polychromatic418967fa.accept_14_10_4_7_1_1214 38 60 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 60 119 (accept_3_2 37 60 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  60 119 (Polychromatic418967fa.accept_13_10_8_2_1_3829 36 60 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 60 119 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 60 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 60 119 (accept_3_2 34 60 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 60 119 (Polychromatic418967fa.accept_13_7_8_2_1_1483 33 60 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 60 119
  (Polychromatic418967fa.accept_9_5_6_2_1_161 32 60 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 60 119 (accept_3_2 31 60 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  60 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 60 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 60 119 (Polychromatic418967fa.accept_11_7_5_9_1_884 29 60 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 60 119 (accept_3_2 28 60 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 60 119 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 60 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 60 119
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 60 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 60 119 (accept_3_2 25 60 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  60 119 (Polychromatic418967fa.accept_14_10_4_7_1_1214 24 60 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 60 119 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 60 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 60 119 (accept_3_2 22 60 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 60 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 60 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 60 119
  (Polychromatic418967fa.accept_13_7_8_2_1_1483 20 60 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 60 119 (accept_3_2 19 60 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  60 119 (Polychromatic418967fa.accept_11_7_5_9_1_884 18 60 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 60 119 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 60 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 60 119 (accept_3_2 16 60 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 60 119 (Polychromatic418967fa.accept_18_15_6_11_1_5651 15 60 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 60 119
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 60 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 60 119 (accept_3_2 13 60 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  60 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 60 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 60 119 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 60 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 60 119 (accept_3_2 10 60 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 60 119 (Polychromatic418967fa.accept_21_9_18_14_1_5648 9 60 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 60 119
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 60 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 60 119 (accept_3_2 7 60 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 60
  119 (Polychromatic418967fa.accept_13_6_8_2_1_1484 6 60 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 60 119 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 60 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 60 119 (accept_3_2 4 60 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 60 119 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 60 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 60 119
  (Polychromatic418967fa.accept_16_2_12_7_1_3410 2 60 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 60 119 (accept_3_2 1 60 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  119)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 119 (allA_succ_of_accept 58 59 119
  (accept_3_2 58 59 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 119
  (Polychromatic418967fa.accept_9_3_5_2_1_28 57 59 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 119 (Polychromatic418967fa.accept_19_18_2_5_1_5682 56 59 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 119 (accept_3_2 55 59 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 119 (Polychromatic418967fa.accept_19_16_2_5_1_5681 54 59 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 119
  (Polychromatic418967fa.accept_9_8_5_2_1_422 53 59 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 119 (accept_3_2 52 59 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 119 (Polychromatic418967fa.accept_9_6_5_2_1_421 51 59 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 119 (Polychromatic418967fa.accept_16_2_11_7_1_2352 50 59 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 119 (accept_3_2 49 59 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 119 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 59 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 119
  (Polychromatic418967fa.accept_13_8_7_2_1_2988 47 59 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 119 (accept_3_2 46 59 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 119 (Polychromatic418967fa.accept_19_7_2_5_1_5680 45 59 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 119 (Polychromatic418967fa.accept_8_4_3_7_1_491 44 59 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 119 (accept_3_2 43 59 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 119 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 59 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 119
  (Polychromatic418967fa.accept_19_3_2_5_1_5679 41 59 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 119 (accept_3_2 40 59 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 119 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 59 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 119 (Polychromatic418967fa.accept_14_10_3_7_1_1975 38 59 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 119 (accept_3_2 37 59 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 119 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 59 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 119
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 59 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 119 (accept_3_2 34 59 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 119 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 59 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 119 (Polychromatic418967fa.accept_14_4_3_7_1_3702 32 59 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 119 (accept_3_2 31 59 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 119 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 59 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 119
  (Polychromatic418967fa.accept_19_10_2_5_1_3059 29 59 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 119 (accept_3_2 28 59 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 119 (Polychromatic418967fa.accept_19_8_2_5_1_5678 27 59 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 119 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 59 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 119 (accept_3_2 25 59 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 119 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 59 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 119
  (Polychromatic418967fa.accept_19_4_2_5_1_5677 23 59 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 119 (accept_3_2 22 59 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 119 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 59 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 119 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 59 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 119 (accept_3_2 19 59 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 119 (Polychromatic418967fa.accept_13_5_7_2_1_852 18 59 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 119
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 59 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 119 (accept_3_2 16 59 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 119 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 59 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 119 (Polychromatic418967fa.accept_18_14_5_11_1_5676 14 59 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 119 (accept_3_2 13 59 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 119 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 59 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 119
  (Polychromatic418967fa.accept_14_11_3_7_1_604 11 59 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 119 (accept_3_2 10 59 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 119 (Polychromatic418967fa.accept_13_9_7_2_1_3869 9 59 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 119 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 59 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 119 (accept_3_2 7 59 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 119 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 59 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 119
  (Polychromatic418967fa.accept_13_5_7_2_1_852 5 59 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 119 (accept_3_2 4 59 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  119 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 59 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 119 (Polychromatic418967fa.accept_11_2_4_9_1_484 2 59 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 119 (accept_3_2 1 59 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 119))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 119 (allA_of_3_0
  58 58 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 119 (allA_succ_of_accept 56 57 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 57 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 119 (accept_3_2 55 57 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 57 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 119 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 57 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 119 (accept_3_2 52 57 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 119 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 57 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 119
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 57 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 119 (accept_3_2 49 57 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 119 (Polychromatic418967fa.accept_10_8_7_9_1_425 48 57 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 119 (Polychromatic418967fa.accept_15_2_12_14_1_1709 47 57 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 119 (accept_3_2 46 57 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 119 (Polychromatic418967fa.accept_16_13_9_7_1_4532 45 57
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 57 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 119 (accept_3_2 43 57 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 57 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 119 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 57 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 119 (accept_3_2 40 57 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 119 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 57 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 119
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 57 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 119 (accept_3_2 37 57 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 119 (Polychromatic418967fa.accept_13_10_5_2_1_1477 36 57 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 119 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 57 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 119 (accept_3_2 34 57 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 119 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 57 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 57 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 119 (accept_3_2 31 57 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 57 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 119 (Polychromatic418967fa.accept_11_7_2_9_1_480 29 57 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 119 (accept_3_2 28 57 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 119 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 57 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 119
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 57 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 119 (accept_3_2 25 57 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 119 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 57 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 119 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 57 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 119 (accept_3_2 22 57 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 119 (Polychromatic418967fa.accept_22_21_13_9_1_5675 21 57 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 57 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 119 (accept_3_2 19 57 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 57 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 119 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 57 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 119 (accept_3_2 16 57 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 119 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 57 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 119
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 57 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 119 (accept_3_2 13 57 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 119 (Polychromatic418967fa.accept_10_2_7_9_1_783 12 57 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 119 (Polychromatic418967fa.accept_15_11_12_14_1_2612 11 57 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 119 (accept_3_2 10 57 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 119 (Polychromatic418967fa.accept_13_9_5_2_1_2185 9 57 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 57 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 119 (accept_3_2 7 57 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  119 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 57 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 119 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 57 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 119 (accept_3_2 4 57 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 119 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 57 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 57
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 119 (accept_3_2 1 57 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 119)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 119 (allA_succ_of_accept 55 56 119 (accept_3_2 55 56 119 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 56 119 (Polychromatic418967fa.accept_11_10_1_9_1_2060 54 56 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 56 119 (Polychromatic418967fa.accept_10_3_6_9_1_779 53 56 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 119 (accept_3_2 52 56 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 56 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 51
  56 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 119
  (Polychromatic418967fa.accept_12_2_8_11_1_31 50 56 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 49 56 119 7 7 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 48 56 119 (Polychromatic418967fa.accept_15_3_11_14_1_1705 48 56 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 56 119 (Polychromatic418967fa.accept_16_15_8_7_1_3407 47 56
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 119 (accept_3_2 46 56 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 56 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 45
  56 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 119
  (Polychromatic418967fa.accept_13_5_4_2_1_846 44 56 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 119 (accept_3_2 43 56 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56
  119 7 6 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  56 119 (Polychromatic418967fa.accept_16_9_8_7_1_4529 41 56 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 56 119 (accept_3_2 40 56 119 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 56 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 56 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 119 (Polychromatic418967fa.accept_12_2_8_11_1_31 38 56 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 56 119 (accept_3_2 37 56 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 56 119 (Polychromatic418967fa.accept_16_4_8_7_1_3396
  36 56 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 56 119 7 5 8 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 56 119 (accept_3_2 34
  56 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 119
  (Polychromatic418967fa.accept_6_3_2_5_1_32 33 56 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 56 119 (Polychromatic418967fa.accept_11_10_1_9_1_2060 32 56 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 56 119 (accept_3_2 31 56 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 56 119 (Polychromatic418967fa.accept_20_10_16_19_1_5674 30 56 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 56 119
  (Polychromatic418967fa.accept_19_10_18_5_1_5673 29 56 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 56 119 7 4 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 56 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 56 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 119 (Polychromatic418967fa.accept_12_2_8_11_1_31 26 56 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 56 119 (accept_3_2 25 56 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 56 119 (Polychromatic418967fa.accept_13_11_4_2_1_2954
  24 56 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 56 119
  (Polychromatic418967fa.accept_10_3_6_9_1_779 23 56 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 56 119 (accept_3_2 22 56 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 56
  119 7 3 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20
  56 119 (Polychromatic418967fa.accept_16_4_8_7_1_3396 20 56 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 56 119 (accept_3_2 19 56 119 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 56 119 (Polychromatic418967fa.accept_13_5_4_2_1_846 18 56 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 56 119 (Polychromatic418967fa.accept_16_1_8_7_1_3377 17 56 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 119 (accept_3_2 16 56 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 15
  56 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 119 7 2 8 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 119 (accept_3_2 13
  56 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 56 119
  (Polychromatic418967fa.accept_13_12_4_2_1_2955 12 56 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 56 119 (Polychromatic418967fa.accept_13_11_4_2_1_2954 11 56 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 119 (accept_3_2 10 56 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 56 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 56 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 119 (Polychromatic418967fa.accept_27_8_2_11_1_5672
  8 56 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 56 119 7 1 8 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 56 119
  (Polychromatic418967fa.accept_13_6_4_2_1_1433 6 56 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 56 119 (Polychromatic418967fa.accept_10_5_6_9_1_2235 5 56 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 119 (accept_3_2 4 56 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 56 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 56 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 119 (Polychromatic418967fa.accept_12_2_8_11_1_31 2
  56 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 119 (accept_3_2 1 56 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 119))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 119 (allA_of_3_0 55 55 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 119
  (allA_succ_of_accept 53 54 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 54 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 119 (accept_3_2 52 54 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 54 119 (Polychromatic418967fa.accept_14_9_12_7_1_597 51 54 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 119 (Polychromatic418967fa.accept_15_5_9_14_1_1724
  50 54 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 119 (accept_3_2 49
  54 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 119
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 48 54 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 54 119 (Polychromatic418967fa.accept_14_5_12_7_1_2767 47 54 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 119 (accept_3_2 46 54 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 54 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 54 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 119 (Polychromatic418967fa.accept_14_2_12_7_1_617
  44 54 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 119 (accept_3_2 43
  54 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 119
  (Polychromatic418967fa.accept_15_12_9_14_1_2635 42 54 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 54 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 54 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 119 (accept_3_2 40 54 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 54 119 (Polychromatic418967fa.accept_19_1_16_5_1_5671 39 54 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 119
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 38 54 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 54 119 (accept_3_2 37 54 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  54 119 (Polychromatic418967fa.accept_15_6_9_14_1_3457 36 54 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 54 119 (Polychromatic418967fa.accept_10_5_4_9_1_420 35 54 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 54 119 (accept_3_2 34 54 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 54 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 54 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 119
  (Polychromatic418967fa.accept_21_11_12_14_1_5670 32 54 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 54 119 (accept_3_2 31 54 119 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 54 119 (Polychromatic418967fa.accept_11_8_10_9_1_1401 30 54 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 54 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 54 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 119 (accept_3_2 28 54 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 54 119
  (Polychromatic418967fa.accept_15_12_9_14_1_2635 27 54 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 54 119 (Polychromatic418967fa.accept_20_6_14_19_1_5669 26 54 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 119 (accept_3_2 25 54 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 54 119 (Polychromatic418967fa.accept_20_4_14_19_1_4222 24 54 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 54 119
  (Polychromatic418967fa.accept_10_3_4_9_1_15 23 54 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 54 119 (accept_3_2 22 54 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  54 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 54 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 54 119 (Polychromatic418967fa.accept_15_5_9_14_1_1724 20 54 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 119 (accept_3_2 19 54 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 54 119 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 54 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 54 119
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 54 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 54 119 (accept_3_2 16 54 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  54 119 (Polychromatic418967fa.accept_10_5_4_9_1_420 15 54 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 54 119 (Polychromatic418967fa.accept_19_14_16_5_1_5668 14 54 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 119 (accept_3_2 13 54 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 54 119 (Polychromatic418967fa.accept_11_1_10_9_1_871 12 54 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 54 119
  (Polychromatic418967fa.accept_19_11_16_5_1_5667 11 54 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 54 119 (accept_3_2 10 54 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  54 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 54 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 54 119 (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 54 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 119 (accept_3_2 7 54 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 54 119 (Polychromatic418967fa.accept_15_6_9_14_1_3457 6 54 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 54 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 54
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 119 (accept_3_2 4 54 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 54 119 (Polychromatic418967fa.accept_10_3_4_9_1_15 3
  54 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 119
  (Polychromatic418967fa.accept_14_2_12_7_1_617 2 54 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 54 119 (accept_3_2 1 54 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  119)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 119 (allA_succ_of_accept 52 53 119 (accept_3_2
  52 53 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 119
  (Polychromatic418967fa.accept_9_6_8_2_1_410 51 53 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 53 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 119 (accept_3_2 49 53 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 119 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 53 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 119 (Polychromatic418967fa.accept_19_9_15_5_1_5666
  47 53 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 119 (accept_3_2 46
  53 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 119
  (Polychromatic418967fa.accept_13_6_1_2_1_1464 45 53 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 53 119 (Polychromatic418967fa.accept_10_4_3_9_1_1262 44 53 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 119 (accept_3_2 43 53 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 53 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 53 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 119 (Polychromatic418967fa.accept_9_5_8_2_1_409 41
  53 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 119 (accept_3_2 40 53
  119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 119
  (Polychromatic418967fa.accept_9_3_8_2_1_162 39 53 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 53 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 53 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 119 (accept_3_2 37 53 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 53 119 (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 53 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 119 (Polychromatic418967fa.accept_13_9_1_2_1_2952
  35 53 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 53 119 (accept_3_2 34
  53 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 53 119
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 53 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 53 119 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 53 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 119 (accept_3_2 31 53 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 53 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 53 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 119 (Polychromatic418967fa.accept_13_3_1_2_1_2960
  29 53 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 119 (accept_3_2 28
  53 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 53 119
  (Polychromatic418967fa.accept_16_11_5_7_1_2395 27 53 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 53 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 53 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 119 (accept_3_2 25 53 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 53 119 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 53 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 119 (Polychromatic418967fa.accept_9_5_8_2_1_409 23
  53 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 53 119 (accept_3_2 22 53
  119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 53 119
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 53 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 53 119 (Polychromatic418967fa.accept_15_5_8_14_1_432 20 53 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 119 (accept_3_2 19 53 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 53 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 53 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 119 (Polychromatic418967fa.accept_14_3_11_7_1_1260
  17 53 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 119 (accept_3_2 16
  53 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 53 119
  (Polychromatic418967fa.accept_9_6_8_2_1_410 15 53 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 53 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 53 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 119 (accept_3_2 13 53 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 53 119 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 53 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 119 (Polychromatic418967fa.accept_16_11_5_7_1_2395
  11 53 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 119 (accept_3_2 10
  53 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 53 119
  (Polychromatic418967fa.accept_13_9_1_2_1_2952 9 53 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 53 119 (Polychromatic418967fa.accept_21_8_11_14_1_5665 8 53 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 119 (accept_3_2 7 53 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 53 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 53 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 119 (Polychromatic418967fa.accept_9_5_8_2_1_409 5
  53 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 53 119 (accept_3_2 4 53 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53 119 (Polychromatic418967fa.accept_9_3_8_2_1_162 3
  53 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 53 119
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 53 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 53 119 (accept_3_2 1 53 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 53
  119))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 119 (allA_of_3_0 52 52 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 51 119 (allA_succ_of_accept 50 51 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 51
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 119 (accept_3_2 49 51 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 51 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 48
  51 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 119
  (Polychromatic418967fa.accept_14_5_9_7_1_590 47 51 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 51 119 (accept_3_2 46 51 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  51 119 (Polychromatic418967fa.accept_10_5_1_9_1_791 45 51 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 51 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 51 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 119 (accept_3_2 43 51 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 51 119 (Polychromatic418967fa.accept_10_2_1_9_1_1248 42 51 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 119
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 51 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 51 119 (accept_3_2 40 51 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  51 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 51 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 51 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 51 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 119 (accept_3_2 37 51 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 51 119 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 51 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 119
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 51 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 51 119 17 2 3 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 51 119 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 51 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 51 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 119 (accept_3_2 31 51 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 51 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 30
  51 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 119
  (Polychromatic418967fa.accept_13_3_12_2_1_385 29 51 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 51 119 (accept_3_2 28 51 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  51 119 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 51 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 51 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 51 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 119 (accept_3_2 25 51 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 51 119 (Polychromatic418967fa.accept_11_2_7_9_1_890 24 51 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 119
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 51 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 51 119 (accept_3_2 22 51 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  51 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 51 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 51 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 51 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 119 (accept_3_2 19 51 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 51 119 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 51 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 17 51 119 17 1 3 7 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 16 51 119 (accept_3_2 16 51 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 119 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 51 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 51 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 119 (accept_3_2 13 51 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 119 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 51 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 119 (Polychromatic418967fa.accept_16_11_3_7_1_2375 11 51 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 119 (accept_3_2 10 51 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 119 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 51 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 51 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 119 (accept_3_2 7 51 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  119 (Polychromatic418967fa.accept_13_6_12_2_1_4707 6 51 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 51 119 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 51 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 119 (accept_3_2 4 51 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 51 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 51 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 51 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 51 119 (accept_3_2 1 51 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  119))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 119 (allA_succ_of_accept 49 50 119 (accept_3_2 49
  50 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 50 119
  (Polychromatic418967fa.accept_9_3_5_2_1_28 48 50 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 50 119 (Polychromatic418967fa.accept_11_3_6_9_1_1378 47 50 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 119 (accept_3_2 46 50 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 50 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 50 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 119 (Polychromatic418967fa.accept_9_8_5_2_1_422 44
  50 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 50 119 (accept_3_2 43 50
  119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 50 119
  (Polychromatic418967fa.accept_9_6_5_2_1_421 42 50 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 50 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 50 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 50 119 (accept_3_2 40 50 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 50 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 50 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 119 (Polychromatic418967fa.accept_15_8_5_14_1_986
  38 50 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 50 119 (accept_3_2 37
  50 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 50 119
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 50 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 50 119 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 50 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 119 (accept_3_2 34 50 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 50 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 50 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 119 (Polychromatic418967fa.accept_12_8_2_11_1_246
  32 50 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 50 119 (accept_3_2 31
  50 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 50 119
  (Polychromatic418967fa.accept_9_3_5_2_1_28 30 50 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 50 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 50 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 119 (accept_3_2 28 50 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 50 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 50 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 119 (Polychromatic418967fa.accept_9_8_5_2_1_422 26
  50 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 50 119 (accept_3_2 25 50
  119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 50 119
  (Polychromatic418967fa.accept_9_6_5_2_1_421 24 50 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 50 119 (Polychromatic418967fa.accept_13_10_11_2_1_3862 23 50 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 119 (accept_3_2 22 50 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 50 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 50 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 119 (Polychromatic418967fa.accept_12_8_2_11_1_246
  20 50 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 50 119 (accept_3_2 19
  50 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 50 119
  (Polychromatic418967fa.accept_24_18_2_23_1_5664 18 50 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 50 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 50 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 119 (accept_3_2 16 50 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 50 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 50 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 119 (Polychromatic418967fa.accept_11_3_6_9_1_1378
  14 50 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 50 119 (accept_3_2 13
  50 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 50 119
  (Polychromatic418967fa.accept_9_3_5_2_1_28 12 50 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 50 119 (Polychromatic418967fa.accept_16_11_2_7_1_3374 11 50 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 119 (accept_3_2 10 50 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 50 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 50 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 119 (Polychromatic418967fa.accept_9_8_5_2_1_422 8
  50 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 50 119 (accept_3_2 7 50 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50 119 (Polychromatic418967fa.accept_9_6_5_2_1_421 6
  50 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 50 119
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 50 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 50 119 (accept_3_2 4 50 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 50
  119 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 50 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 50 119 (Polychromatic418967fa.accept_15_2_5_14_1_61 2 50 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 119 (accept_3_2 1 50 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 50 119)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 119 (allA_of_3_0 49 49
  119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 119 (allA_succ_of_accept 47 48 119
  (Polychromatic418967fa.accept_10_7_8_9_1_785 47 48 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 48 119 (accept_3_2 46 48 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  48 119 (Polychromatic418967fa.accept_13_6_9_2_1_838 45 48 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 48 119 (Polychromatic418967fa.accept_9_8_3_2_1_417 44 48 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 119 (accept_3_2 43 48 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 119 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 48 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 48 119
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 48 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 48 119 (accept_3_2 40 48 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  48 119 (Polychromatic418967fa.accept_21_18_6_14_1_2812 39 48 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 48 119 (Polychromatic418967fa.accept_22_16_4_9_1_5663 38 48 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 119 (accept_3_2 37 48 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 119 (Polychromatic418967fa.accept_14_8_6_7_1_1934 36 48 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 48 119
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 48 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 48 119 (accept_3_2 34 48 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  48 119 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 48 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 48 119 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 48 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 119 (accept_3_2 31 48 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 119 (Polychromatic418967fa.accept_19_11_10_5_1_5662 30 48 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 48 119
  (Polychromatic418967fa.accept_13_3_9_2_1_1486 29 48 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 48 119 (accept_3_2 28 48 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  48 119 (Polychromatic418967fa.accept_10_7_8_9_1_785 27 48 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 48 119 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 48 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 119 (accept_3_2 25 48 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 119 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 48 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 48 119
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 48 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 48 119 (accept_3_2 22 48 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  48 119 (Polychromatic418967fa.accept_10_1_8_9_1_787 21 48 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 48 119 (Polychromatic418967fa.accept_13_7_9_2_1_2167 20 48 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 119 (accept_3_2 19 48 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 119 (Polychromatic418967fa.accept_13_5_9_2_1_1489 18 48 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 48 119
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 48 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 48 119 (accept_3_2 16 48 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  48 119 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 48 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 48 119 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 48 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 119 (accept_3_2 13 48 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 119 (Polychromatic418967fa.accept_21_12_6_14_1_4146 12 48 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 48 119
  (Polychromatic418967fa.accept_10_1_8_9_1_787 11 48 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 48 119 (accept_3_2 10 48 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  48 119 (Polychromatic418967fa.accept_18_9_12_11_1_5642 9 48 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 48 119 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 48 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 119 (accept_3_2 7 48 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 119 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 48 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 48 119
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 48 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 48 119 (accept_3_2 4 48 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 48
  119 (Polychromatic418967fa.accept_13_3_9_2_1_1486 3 48 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 48 119 (Polychromatic418967fa.accept_11_2_4_9_1_484 2 48 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 119 (accept_3_2 1 48 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 48 119)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 119
  (allA_succ_of_accept 46 47 119 (accept_3_2 46 47 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  47 119 (Polychromatic418967fa.accept_13_6_8_2_1_1484 45 47 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 47 119 (Polychromatic418967fa.accept_14_2_5_7_1_3767 44 47 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 119 (accept_3_2 43 47 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 47 119 (Polychromatic418967fa.accept_10_2_7_9_1_783 42 47 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 119
  (Polychromatic418967fa.accept_21_20_5_14_1_5661 41 47 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 119 (accept_3_2 40 47 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  47 119 (Polychromatic418967fa.accept_11_6_3_9_1_906 39 47 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 47 119 (Polychromatic418967fa.accept_10_8_7_9_1_425 38 47 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 119 (accept_3_2 37 47 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 119 (Polychromatic418967fa.accept_13_10_8_2_1_3829 36 47 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 119
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 35 47 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 119 (accept_3_2 34 47 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 119 (Polychromatic418967fa.accept_13_7_8_2_1_1483 33 47 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 119 (Polychromatic418967fa.accept_10_2_7_9_1_783 32 47 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 119 (accept_3_2 31 47 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 119 (Polychromatic418967fa.accept_14_2_5_7_1_3767 30 47 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 119
  (Polychromatic418967fa.accept_21_8_5_14_1_5660 29 47 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 119 (accept_3_2 28 47 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 119 (Polychromatic418967fa.accept_15_12_2_14_1_5659 27 47 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 119 (Polychromatic418967fa.accept_14_12_5_7_1_2010 26 47 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 119 (accept_3_2 25 47 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 119 (Polychromatic418967fa.accept_16_8_15_7_1_5658 24 47
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 119
  (Polychromatic418967fa.accept_13_10_8_2_1_3829 23 47 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 119 (accept_3_2 22 47 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 119 (Polychromatic418967fa.accept_23_21_1_4_1_5657 21 47 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 119 (Polychromatic418967fa.accept_13_7_8_2_1_1483 20 47 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 119 (accept_3_2 19 47 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 119 (Polychromatic418967fa.accept_10_8_7_9_1_425 18 47 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 119
  (Polychromatic418967fa.accept_11_6_3_9_1_906 17 47 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 119 (accept_3_2 16 47 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 119 (Polychromatic418967fa.accept_19_15_9_5_1_5656 15 47 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 119 (Polychromatic418967fa.accept_16_14_15_7_1_5655 14 47 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 119 (accept_3_2 13 47 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 119 (Polychromatic418967fa.accept_10_2_7_9_1_783 12 47 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 119
  (Polychromatic418967fa.accept_16_11_15_7_1_5654 11 47 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 119 (accept_3_2 10 47 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 119 (Polychromatic418967fa.accept_14_9_5_7_1_1251 9 47 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 119 (Polychromatic418967fa.accept_10_8_7_9_1_425 8 47 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 119 (accept_3_2 7 47 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 119 (Polychromatic418967fa.accept_11_6_3_9_1_906 6 47 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 119
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 5 47 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 119 (accept_3_2 4 47 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  119 (Polychromatic418967fa.accept_15_3_2_14_1_1713 3 47 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 47 119 (Polychromatic418967fa.accept_10_2_7_9_1_783 2 47 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 119 (accept_3_2 1 47 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 47 119))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 119 (allA_of_3_0 46
  46 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 119 (allA_succ_of_accept 44 45 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 45 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 119 (accept_3_2 43 45 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 45 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 119 (Polychromatic418967fa.accept_10_1_5_9_1_157 41 45 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 119 (accept_3_2 40 45 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 119 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 45 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 119
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 45 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 119 (accept_3_2 37 45 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  45 119 (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 45 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 45 119 (Polychromatic418967fa.accept_13_9_6_2_1_2200 35 45 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 119 (accept_3_2 34 45 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 119 (Polychromatic418967fa.accept_18_15_9_11_1_4371 33 45 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 45 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 119 (accept_3_2 31 45 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  45 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 45 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 45 119 (Polychromatic418967fa.accept_19_10_7_5_1_5653 29 45 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 119 (accept_3_2 28 45 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 119 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 45 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 119
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 45 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 119 (accept_3_2 25 45 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  45 119 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 45 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 119 (Polychromatic418967fa.accept_13_10_6_2_1_1440 23 45 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 119 (accept_3_2 22 45 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 119 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 45 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 45 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 119 (accept_3_2 19 45 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  45 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 45 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 119 (Polychromatic418967fa.accept_13_4_6_2_1_1437 17 45 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 119 (accept_3_2 16 45 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 119 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 45 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 119
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 45 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 119 (accept_3_2 13 45 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  45 119 (Polychromatic418967fa.accept_13_12_6_2_1_1441 12 45 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 119 (Polychromatic418967fa.accept_10_1_5_9_1_157 11 45 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 119 (accept_3_2 10 45 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 119 (Polychromatic418967fa.accept_13_9_6_2_1_2200 9 45 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 45 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 119 (accept_3_2 7 45 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  119 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 45 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 119 (Polychromatic418967fa.accept_22_5_1_9_1_5652 5 45 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 119 (accept_3_2 4 45 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 119 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 45 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 45
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 119 (accept_3_2 1 45 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 119))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  119 (allA_succ_of_accept 43 44 119 (accept_3_2 43 44 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 44 119 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 44 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 44 119 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 44 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 119 (accept_3_2 40 44 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 44 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 44 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 119
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 38 44 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 44 119 (accept_3_2 37 44 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  44 119 (Polychromatic418967fa.accept_13_10_5_2_1_1477 36 44 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 44 119 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 44 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 119 (accept_3_2 34 44 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 44 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 44 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 119
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 44 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 44 119 (accept_3_2 31 44 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  44 119 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 44 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 44 119 (Polychromatic418967fa.accept_13_3_5_2_1_1475 29 44 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 119 (accept_3_2 28 44 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 44 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 44 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 119
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 44 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 44 119 (accept_3_2 25 44 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  44 119 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 44 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 44 119 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 44 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 119 (accept_3_2 22 44 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 44 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 44 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 119
  (Polychromatic418967fa.accept_13_7_5_2_1_401 20 44 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 44 119 (accept_3_2 19 44 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  44 119 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 44 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 44 119 (Polychromatic418967fa.accept_13_4_5_2_1_1436 17 44 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 119 (accept_3_2 16 44 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 44 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 44 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 119
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 44 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 44 119 (accept_3_2 13 44 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  44 119 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 44 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 44 119 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 44 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 119 (accept_3_2 10 44 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 44 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 44 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 119
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 44 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 44 119 (accept_3_2 7 44 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44
  119 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 44 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 44 119 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 44 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 44 119 (accept_3_2 4 44 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 44 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 44 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 44 119 (Polychromatic418967fa.accept_12_2_8_11_1_31 2
  44 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 119 (accept_3_2 1 44 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 119)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43
  119 (allA_of_3_0 43 43 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 119 (allA_succ_of_accept 41 42 119
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 42 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 119 (accept_3_2 40 42 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  42 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 42 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 42 119 (Polychromatic418967fa.accept_13_12_3_2_1_1470 38 42 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 119 (accept_3_2 37 42 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 119 (Polychromatic418967fa.accept_13_10_3_2_1_4728 36 42
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 42 119 7 5 6 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 42 119 (accept_3_2 34
  42 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 42 119
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 42 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 42 119 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 42 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 119 (accept_3_2 31 42 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 42 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 42 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 42 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 29
  42 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 119 7 4 6 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 42 119
  (Polychromatic418967fa.accept_10_7_2_9_1_775 27 42 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 42 119 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 42 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 119 (accept_3_2 25 42 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 42 119 (Polychromatic418967fa.accept_13_11_3_2_1_863 24 42 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 42 119 (Polychromatic418967fa.accept_9_5_6_2_1_161 23
  42 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 42 119 (accept_3_2 22 42
  119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 42 119 7 3 6 17 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 42 119
  (Polychromatic418967fa.accept_19_1_4_5_1_4313 20 42 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 42 119 (accept_3_2 19 42 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  42 119 (Polychromatic418967fa.accept_13_5_3_2_1_1499 18 42 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 42 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 42 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 42 119 (accept_3_2 16 42 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 42 119 (Polychromatic418967fa.accept_18_15_6_11_1_5651 15 42 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 119 7 2 6 17 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 119 (accept_3_2 13 42 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 42 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 42 119
  (Polychromatic418967fa.accept_10_1_2_9_1_152 11 42 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 42 119 (accept_3_2 10 42 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  42 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 42 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 42 119 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 42 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 42 119 7 1 6 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 42 119 (Polychromatic418967fa.accept_19_6_4_5_1_5650 6 42 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 42 119
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 42 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 42 119 (accept_3_2 4 42 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 42
  119 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 42 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 42 119 (Polychromatic418967fa.accept_15_2_12_14_1_1709 2 42 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 119 (accept_3_2 1 42 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 42 119)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 119 (allA_succ_of_accept 40 41
  119 (accept_3_2 40 41 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 119
  (Polychromatic418967fa.accept_9_3_5_2_1_28 39 41 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 41 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 119 (accept_3_2 37 41 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 119 (Polychromatic418967fa.accept_14_8_13_7_1_2798 36 41 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 119
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 41 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 119 (accept_3_2 34 41 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 119 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 41 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 119 (Polychromatic418967fa.accept_10_2_1_9_1_1248 32 41 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 119 (accept_3_2 31 41 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 41 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 119
  (Polychromatic418967fa.accept_14_1_13_7_1_1205 29 41 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 119 (accept_3_2 28 41 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 119 (Polychromatic418967fa.accept_15_12_11_14_1_3464 27 41 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 41 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 119 (accept_3_2 25 41 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 119 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 41 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 119
  (Polychromatic418967fa.accept_21_2_20_14_1_5649 23 41 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 119 (accept_3_2 22 41 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 119 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 41 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 119 (Polychromatic418967fa.accept_14_6_13_7_1_2015 20 41 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 119 (accept_3_2 19 41 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 41 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 119
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 41 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 119 (accept_3_2 16 41 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 119 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 41 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 41 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 119 (accept_3_2 13 41 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 119 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 41 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 119
  (Polychromatic418967fa.accept_21_11_20_14_1_4179 11 41 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 41 119 (accept_3_2 10 41 119 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 41 119 (Polychromatic418967fa.accept_21_9_20_14_1_4139 9 41 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 119 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 41 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 119 (accept_3_2 7 41 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 41
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 119
  (Polychromatic418967fa.accept_10_5_1_9_1_791 5 41 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 119 (accept_3_2 4 41 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  119 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 41 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 41 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 119 (accept_3_2 1 41 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 119))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 119 (allA_of_3_0 40 40 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 119 (allA_succ_of_accept 38 39 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 39 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 119 (accept_3_2 37 39 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 119 (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 39 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 119 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 39 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 119 (accept_3_2 34 39 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 119 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 39 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 39 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 119 (accept_3_2 31 39 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 119 (Polychromatic418967fa.accept_21_9_18_14_1_5648 30 39 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 119 (Polychromatic418967fa.accept_24_5_15_23_1_5647 29 39 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 119 (accept_3_2 28 39 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 119 (Polychromatic418967fa.accept_15_12_9_14_1_2635 27 39
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 39 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 119 (accept_3_2 25 39 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 119 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 39 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 119 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 39 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 119 (accept_3_2 22 39 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 119 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 39 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 39 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 119 (accept_3_2 19 39 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 119 (Polychromatic418967fa.accept_14_4_11_7_1_1234 18 39 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 119 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 39 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 119 (accept_3_2 16 39 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 119 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 39 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 39 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 119 (accept_3_2 13 39 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 119 (Polychromatic418967fa.accept_15_12_9_14_1_2635 12 39 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 119 (Polychromatic418967fa.accept_21_11_18_14_1_5646 11 39 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 119 (accept_3_2 10 39 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 119 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 39 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 39 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 119 (accept_3_2 7 39 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  119 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 39 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 119 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 39 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 119 (accept_3_2 4 39 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 119 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 39 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 39
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 119 (accept_3_2 1 39 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 119))))))))))))))))))))))))))))))))))))))) (allB_succ 38 119
  (allA_succ_of_accept 37 38 119 (accept_3_2 37 38 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 119 (Polychromatic418967fa.accept_13_10_12_2_1_1460 36 38 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 119 (Polychromatic418967fa.accept_15_5_8_14_1_432 35 38 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 119 (accept_3_2 34 38 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 38 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 119
  (Polychromatic418967fa.accept_12_8_2_11_1_246 32 38 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 119 (accept_3_2 31 38 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 119 (Polychromatic418967fa.accept_13_4_12_2_1_1459 30 38 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 38 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 119 (accept_3_2 28 38 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 38 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 119
  (Polychromatic418967fa.accept_21_5_17_14_1_4178 26 38 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 119 (accept_3_2 25 38 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 119 (Polychromatic418967fa.accept_10_4_8_9_1_784 24 38 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 119 (Polychromatic418967fa.accept_13_10_12_2_1_1460 23 38 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 119 (accept_3_2 22 38 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 38 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 119
  (Polychromatic418967fa.accept_12_8_2_11_1_246 20 38 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 119 (accept_3_2 19 38 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 119 (Polychromatic418967fa.accept_11_7_5_9_1_884 18 38 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 38 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 119 (accept_3_2 16 38 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 38 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 119
  (Polychromatic418967fa.accept_10_4_8_9_1_784 14 38 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 119 (accept_3_2 13 38 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 119 (Polychromatic418967fa.accept_23_12_15_4_1_5645 12 38 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 119 (Polychromatic418967fa.accept_10_1_8_9_1_787 11 38 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 119 (accept_3_2 10 38 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 38 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 119
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 38 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 119 (accept_3_2 7 38 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  119 (Polychromatic418967fa.accept_13_6_12_2_1_4707 6 38 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 38 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 38 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 119 (accept_3_2 4 38 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 38 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 38 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 119
  (Polychromatic418967fa.accept_21_2_17_14_1_5644 2 38 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 38 119 (accept_3_2 1 38 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38
  119)))))))))))))))))))))))))))))))))))))) (allB_succ 37 119 (allA_of_3_0 37 37 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 36 119 (allA_succ_of_accept 35 36 119 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 36 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 36 119 (accept_3_2 34 36 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 36 119 (Polychromatic418967fa.accept_10_3_6_9_1_779
  33 36 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 36 119
  (Polychromatic418967fa.accept_13_6_10_2_1_1449 32 36 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 36 119 (accept_3_2 31 36 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  36 119 (Polychromatic418967fa.accept_16_14_4_7_1_2380 30 36 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 36 119 (Polychromatic418967fa.accept_13_3_10_2_1_381 29 36 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 119 (accept_3_2 28 36 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 36 119 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 36 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 36 119
  (Polychromatic418967fa.accept_19_7_17_5_1_3081 26 36 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 36 119 (accept_3_2 25 36 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  36 119 (Polychromatic418967fa.accept_13_11_10_2_1_3840 24 36 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 36 119 (Polychromatic418967fa.accept_10_3_6_9_1_779 23 36 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 36 119 (accept_3_2 22 36 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 36 119 (Polychromatic418967fa.accept_13_8_10_2_1_1450 21 36 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 36 119
  (Polychromatic418967fa.accept_14_6_8_7_1_589 20 36 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 36 119 (accept_3_2 19 36 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  36 119 (Polychromatic418967fa.accept_13_5_10_2_1_856 18 36 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 36 119 (Polychromatic418967fa.accept_11_6_3_9_1_906 17 36 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 36 119 (accept_3_2 16 36 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 36 119 (Polychromatic418967fa.accept_10_5_6_9_1_2235 15 36 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 36 119
  (Polychromatic418967fa.accept_16_14_4_7_1_2380 14 36 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 36 119 (accept_3_2 13 36 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  36 119 (Polychromatic418967fa.accept_13_12_10_2_1_1451 12 36 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 36 119 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 36 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 36 119 (accept_3_2 10 36 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 36 119 (Polychromatic418967fa.accept_15_9_6_14_1_2627 9 36 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 36 119
  (Polychromatic418967fa.accept_13_8_10_2_1_1450 8 36 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 36 119 (accept_3_2 7 36 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 36
  119 (Polychromatic418967fa.accept_11_6_3_9_1_906 6 36 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 36 119 (Polychromatic418967fa.accept_10_5_6_9_1_2235 5 36 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36 119 (accept_3_2 4 36 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 36 119 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 36 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 36 119 (Polychromatic418967fa.accept_19_2_17_5_1_5643
  2 36 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 119 (accept_3_2 1 36
  119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 119)))))))))))))))))))))))))))))))))))) (allB_succ 35 119
  (allA_succ_of_accept 34 35 119 (accept_3_2 34 35 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  35 119 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 35 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 35 119 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 35 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 119 (accept_3_2 31 35 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 35 119 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 35 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 119
  (Polychromatic418967fa.accept_11_7_2_9_1_480 29 35 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 35 119 7 4 5 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 35 119 (Polychromatic418967fa.accept_13_1_9_2_1_1448 27 35 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 119 (Polychromatic418967fa.accept_10_6_5_9_1_1233 26 35 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 119 (accept_3_2 25 35 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 35 119 (Polychromatic418967fa.accept_9_6_8_2_1_410 24
  35 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 119
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 35 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 119 (accept_3_2 22 35 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 35
  119 7 3 5 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20
  35 119 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 35 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 35 119 (accept_3_2 19 35 119 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 35 119 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 35 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 119 (Polychromatic418967fa.accept_15_2_5_14_1_61 17 35 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 119 (accept_3_2 16 35 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 119 (Polychromatic418967fa.accept_9_6_8_2_1_410 15
  35 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 35 119 7 2 5 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 35 119 (accept_3_2 13
  35 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 119
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 35 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 35 119 (Polychromatic418967fa.accept_10_1_5_9_1_157 11 35 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 119 (accept_3_2 10 35 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 35 119 (Polychromatic418967fa.accept_15_9_5_14_1_973 9 35 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 119 (Polychromatic418967fa.accept_15_8_5_14_1_986 8
  35 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 35 119 7 1 5 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 35 119
  (Polychromatic418967fa.accept_9_6_8_2_1_410 6 35 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 35 119 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 35 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 119 (accept_3_2 4 35 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 35 119 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 35 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 119 (Polychromatic418967fa.accept_15_2_5_14_1_61 2
  35 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 119 (accept_3_2 1 35 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35 119))))))))))))))))))))))))))))))))))) (allB_succ 34 119
  (allA_of_3_0 34 34 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 33 119 (allA_succ_of_accept 32 33 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 33 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 119 (accept_3_2 31 33 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  33 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 33 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 33 119 (Polychromatic418967fa.accept_19_10_14_5_1_3079 29 33 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 119 (accept_3_2 28 33 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 119 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 33 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 119
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 33 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 119 (accept_3_2 25 33 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  33 119 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 33 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 33 119 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 33 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 119 (accept_3_2 22 33 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 33 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 33 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 119 (accept_3_2 19 33 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  33 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 33 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 33 119 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 33 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 119 (accept_3_2 16 33 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 119 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 33 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 119
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 33 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 119 (accept_3_2 13 33 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  33 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 33 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 33 119 (Polychromatic418967fa.accept_15_11_3_14_1_971 11 33 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 119 (accept_3_2 10 33 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 119 (Polychromatic418967fa.accept_13_9_7_2_1_3869 9 33 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 33 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 119 (accept_3_2 7 33 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33
  119 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 33 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 119 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 33 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 119 (accept_3_2 4 33 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 33 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 33 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 33
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 119 (accept_3_2 1 33 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 119))))))))))))))))))))))))))))))))) (allB_succ 32 119
  (allA_succ_of_accept 31 32 119 (accept_3_2 31 32 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  32 119 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 32 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 32 119 (Polychromatic418967fa.accept_19_10_13_5_1_3091 29 32 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 119 (accept_3_2 28 32 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 32 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 32 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 119
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 32 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 32 119 (accept_3_2 25 32 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  32 119 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 32 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 32 119 (Polychromatic418967fa.accept_11_1_10_9_1_871 23 32 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 119 (accept_3_2 22 32 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 32 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 32 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 119
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 20 32 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 32 119 (accept_3_2 19 32 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  32 119 (Polychromatic418967fa.accept_15_3_2_14_1_1713 18 32 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 32 119 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 32 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 119 (accept_3_2 16 32 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 32 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 32 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 119
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 32 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 32 119 (accept_3_2 13 32 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  32 119 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 32 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 32 119 (Polychromatic418967fa.accept_10_1_2_9_1_152 11 32 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 119 (accept_3_2 10 32 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 32 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 119
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 32 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 119 (accept_3_2 7 32 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32
  119 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 32 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 32 119 (Polychromatic418967fa.accept_15_5_2_14_1_1693 5 32 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 119 (accept_3_2 4 32 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 32 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 32 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 119 (Polychromatic418967fa.accept_12_2_8_11_1_31 2
  32 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 119 (accept_3_2 1 32 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 119)))))))))))))))))))))))))))))))) (allB_succ 31 119
  (allA_of_3_0 31 31 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 30 119 (allA_succ_of_accept 29 30 119
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 30 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 30 119 (accept_3_2 28 30 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  30 119 (Polychromatic418967fa.accept_18_9_12_11_1_5642 27 30 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 30 119 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 30 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 119 (accept_3_2 25 30 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 119 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 30 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 119
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 30 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 30 119 (accept_3_2 22 30 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  30 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 30 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 30 119 (Polychromatic418967fa.accept_16_4_14_7_1_5641 20 30 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 119 (accept_3_2 19 30 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 119 (Polychromatic418967fa.accept_13_5_4_2_1_846 18 30 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 119
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 30 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 30 119 (accept_3_2 16 30 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  30 119 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 30 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 30 119 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 30 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 119 (accept_3_2 13 30 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 119 (Polychromatic418967fa.accept_13_12_4_2_1_2955 12 30 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 30 119
  (Polychromatic418967fa.accept_13_11_4_2_1_2954 11 30 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 30 119 (accept_3_2 10 30 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  30 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 30 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 30 119 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 30 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 119 (accept_3_2 7 30 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 30 119 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 30 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 30 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 30
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30 119 (accept_3_2 4 30 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30 119 (Polychromatic418967fa.accept_20_3_10_19_1_5640
  3 30 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 119
  (Polychromatic418967fa.accept_21_2_9_14_1_4189 2 30 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 30 119 (accept_3_2 1 30 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30
  119)))))))))))))))))))))))))))))) (allB_succ 29 119 (allA_succ_of_accept 28 29 119 (accept_3_2 28 29 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 119 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 29 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 119
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 29 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 29 119 (accept_3_2 25 29 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  29 119 (Polychromatic418967fa.accept_11_2_7_9_1_890 24 29 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 29 119 (Polychromatic418967fa.accept_13_10_3_2_1_4728 23 29 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 119 (accept_3_2 22 29 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 119 (Polychromatic418967fa.accept_19_2_10_5_1_5639 21 29
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 119
  (Polychromatic418967fa.accept_14_6_1_7_1_2775 20 29 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 29 119 (accept_3_2 19 29 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  29 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 29 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 29 119 (Polychromatic418967fa.accept_21_17_8_14_1_5638 17 29 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 119 (accept_3_2 16 29 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 119 (Polychromatic418967fa.accept_19_15_10_5_1_5637 15 29
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 119
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 29 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 29 119 (accept_3_2 13 29 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  29 119 (Polychromatic418967fa.accept_13_12_3_2_1_1470 12 29 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 29 119 (Polychromatic418967fa.accept_13_11_3_2_1_863 11 29 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 119 (accept_3_2 10 29 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 119 (Polychromatic418967fa.accept_13_9_3_2_1_399 9 29 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 119
  (Polychromatic418967fa.accept_14_8_1_7_1_3725 8 29 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 29 119 (accept_3_2 7 29 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29
  119 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 29 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 29 119 (Polychromatic418967fa.accept_11_5_7_9_1_2696 5 29 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 119 (accept_3_2 4 29 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 29 119 (Polychromatic418967fa.accept_19_3_10_5_1_4314 3 29 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 29
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 119 (accept_3_2 1 29 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29 119))))))))))))))))))))))))))))) (allB_succ 28 119 (allA_of_3_0
  28 28 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 27 119 (allA_succ_of_accept 26 27 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 27 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 119 (accept_3_2 25 27 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  27 119 (Polychromatic418967fa.accept_15_9_12_14_1_963 24 27 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 27 119 (Polychromatic418967fa.accept_19_4_8_5_1_5636 23 27 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 119 (accept_3_2 22 27 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 119 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 27 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 27 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 119 (accept_3_2 19 27 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  27 119 (Polychromatic418967fa.accept_10_8_7_9_1_425 18 27 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 27 119 (Polychromatic418967fa.accept_15_2_12_14_1_1709 17 27 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 119 (accept_3_2 16 27 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 119 (Polychromatic418967fa.accept_14_1_13_7_1_1205 15 27
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 27 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 119 (accept_3_2 13 27 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  27 119 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 27 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 27 119 (Polychromatic418967fa.accept_15_11_12_14_1_2612 11 27 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 119 (accept_3_2 10 27 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 119 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 27 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 27 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 119 (accept_3_2 7 27 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27
  119 (Polychromatic418967fa.accept_13_6_1_2_1_1464 6 27 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 27 119 (Polychromatic418967fa.accept_16_5_11_7_1_5635 5 27 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 119 (accept_3_2 4 27 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 119 (Polychromatic418967fa.accept_13_3_1_2_1_2960 3 27 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 27 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 27 119 (accept_3_2 1 27 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27
  119))))))))))))))))))))))))))) (allB_succ 26 119 (allA_succ_of_accept 25 26 119 (accept_3_2 25 26 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 119 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 26 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 26 119
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 26 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 26 119 (accept_3_2 22 26 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  26 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 26 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 26 119 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 26 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 119 (accept_3_2 19 26 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 26 119 (Polychromatic418967fa.accept_15_3_11_14_1_1705 18 26 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 26 119
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 26 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 26 119 (accept_3_2 16 26 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  26 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 26 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 26 119 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 26 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 26 119 (accept_3_2 13 26 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 26 119 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 26 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 26 119
  (Polychromatic418967fa.accept_21_11_5_14_1_4142 11 26 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 26 119 (accept_3_2 10 26 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  26 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 26 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 26 119 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 26 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 26 119 (accept_3_2 7 26 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 26 119 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 26 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 26 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 26
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 119 (accept_3_2 4 26 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 26 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 26
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 119
  (Polychromatic418967fa.accept_11_2_4_9_1_484 2 26 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 26 119 (accept_3_2 1 26 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  119)))))))))))))))))))))))))) (allB_succ 25 119 (allA_of_3_0 25 25 119 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 24 119 (allA_succ_of_accept 23 24 119 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 24 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 119 (accept_3_2 22 24 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 24 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 24 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 24 119
  (Polychromatic418967fa.accept_15_5_9_14_1_1724 20 24 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 24 119 (accept_3_2 19 24 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  24 119 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 24 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 24 119 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 24 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 119 (accept_3_2 16 24 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 24 119 (Polychromatic418967fa.accept_10_5_4_9_1_420 15 24 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 24 119
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 24 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 24 119 (accept_3_2 13 24 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  24 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 24 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 24 119 (Polychromatic418967fa.accept_14_11_10_7_1_1948 11 24 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 24 119 (accept_3_2 10 24 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 24 119 (Polychromatic418967fa.accept_13_9_11_2_1_1491 9 24 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 24 119
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 24 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 24 119 (accept_3_2 7 24 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 24
  119 (Polychromatic418967fa.accept_15_6_9_14_1_3457 6 24 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 24 119 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 24 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 119 (accept_3_2 4 24 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 24 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 24 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 119
  (Polychromatic418967fa.accept_20_2_4_19_1_5634 2 24 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 24 119 (accept_3_2 1 24 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24
  119)))))))))))))))))))))))) (allB_succ 23 119 (allA_succ_of_accept 22 23 119 (accept_3_2 22 23 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 119 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 23 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 23 119
  (Polychromatic418967fa.accept_15_5_8_14_1_432 20 23 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 23 119 (accept_3_2 19 23 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  23 119 (Polychromatic418967fa.accept_13_5_10_2_1_856 18 23 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 23 119 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 23 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 119 (accept_3_2 16 23 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 119 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 23 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 119
  (Polychromatic418967fa.accept_10_4_3_9_1_1262 14 23 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 119 (accept_3_2 13 23 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  23 119 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 23 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 119 (Polychromatic418967fa.accept_13_11_10_2_1_3840 11 23 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 119 (accept_3_2 10 23 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 119 (Polychromatic418967fa.accept_15_9_8_14_1_1699 9 23 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 119
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 23 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 119 (accept_3_2 7 23 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  119 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 23 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 119 (Polychromatic418967fa.accept_13_5_10_2_1_856 5 23 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 119 (accept_3_2 4 23 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 23 119 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 23 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 119 (Polychromatic418967fa.accept_14_2_9_7_1_5633 2
  23 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 119 (accept_3_2 1 23 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23 119))))))))))))))))))))))) (allB_succ 22 119 (allA_of_3_0 22 22
  119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 21 119 (allA_succ_of_accept 20 21 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 21 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 119 (accept_3_2 19 21 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  21 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 21 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 21 119 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 21 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 119 (accept_3_2 16 21 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 119 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 21 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 21 119 7 2 3 17 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 21 119 (accept_3_2 13 21 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 119 (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 21 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 119
  (Polychromatic418967fa.accept_16_11_5_7_1_2395 11 21 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 119 (accept_3_2 10 21 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  21 119 (Polychromatic418967fa.accept_15_9_6_14_1_2627 9 21 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 21 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 21 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 21 119 7 1 3 17 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 21 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 21
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 119
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 21 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 21 119 (accept_3_2 4 21 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21
  119 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 21 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 21 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 21 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 119 (accept_3_2 1 21 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 21 119))))))))))))))))))))) (allB_succ 20 119 (allA_succ_of_accept 19 20 119
  (accept_3_2 19 20 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 119
  (Polychromatic418967fa.accept_13_5_7_2_1_852 18 20 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 20 119 (Polychromatic418967fa.accept_15_2_5_14_1_61 17 20 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 119 (accept_3_2 16 20 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 20 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 20 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 20 119 (Polychromatic418967fa.accept_12_2_8_11_1_31
  14 20 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 119 (accept_3_2 13
  20 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 119
  (Polychromatic418967fa.accept_16_12_4_7_1_3391 12 20 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 20 119 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 20 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 20 119 (accept_3_2 10 20 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 20 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 20 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 119 (Polychromatic418967fa.accept_13_8_7_2_1_2988 8
  20 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 119 (accept_3_2 7 20 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 119 (Polychromatic418967fa.accept_15_6_5_14_1_429 6
  20 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 20 119
  (Polychromatic418967fa.accept_13_5_7_2_1_852 5 20 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 20 119 (accept_3_2 4 20 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20
  119 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 20 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 20 119 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 20 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 119 (accept_3_2 1 20 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 119)))))))))))))))))))) (allB_succ 19 119 (allA_of_3_0 19 19 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 18 119 (allA_succ_of_accept 17 18 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 18 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 119 (accept_3_2 16 18 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 18 119
  (Polychromatic418967fa.accept_21_15_18_14_1_5632 15 18 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 18 119 (Polychromatic418967fa.accept_10_4_8_9_1_784 14 18 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 18 119 (accept_3_2 13 18 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 18 119 (Polychromatic418967fa.accept_13_12_5_2_1_2173 12 18 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 18 119
  (Polychromatic418967fa.accept_10_1_8_9_1_787 11 18 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 18 119 (accept_3_2 10 18 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  18 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 18 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 18 119 (Polychromatic418967fa.accept_22_8_18_9_1_5631 8 18 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 18 119 (accept_3_2 7 18 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 18 119 (Polychromatic418967fa.accept_19_6_18_5_1_5630 6 18 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 18 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 18
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 119 (accept_3_2 4 18 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 18 119 (Polychromatic418967fa.accept_13_3_5_2_1_1475 3
  18 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 119
  (Polychromatic418967fa.accept_11_2_7_9_1_890 2 18 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 18 119 (accept_3_2 1 18 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18
  119)))))))))))))))))) (allB_succ 17 119 (allA_succ_of_accept 16 17 119 (accept_3_2 16 17 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 119 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 17 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 119
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 17 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 119 (accept_3_2 13 17 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 119 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 17 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 119 (Polychromatic418967fa.accept_13_11_4_2_1_2954 11 17 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 119 (accept_3_2 10 17 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 119 (Polychromatic418967fa.accept_21_9_17_14_1_603 9 17 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 119
  (Polychromatic418967fa.accept_10_8_7_9_1_425 8 17 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 119 (accept_3_2 7 17 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  119 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 17 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 119 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 17 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 119 (accept_3_2 4 17 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 119 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 17 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 17
  119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 119 (accept_3_2 1 17 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 119))))))))))))))))) (allB_succ 16 119 (allA_of_3_0 16 16 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15 119 (allA_succ_of_accept 14 15 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 15 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 119 (accept_3_2 13 15 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  15 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 15 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 15 119 (Polychromatic418967fa.accept_10_1_5_9_1_157 11 15 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 119 (accept_3_2 10 15 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 119 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 15 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 15 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 119 (accept_3_2 7 15 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15
  119 (Polychromatic418967fa.accept_10_6_5_9_1_1233 6 15 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 15 119 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 15 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 119 (accept_3_2 4 15 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 119 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 15 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 119
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 15 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 119 (accept_3_2 1 15 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15
  119))))))))))))))) (allB_succ 14 119 (allA_succ_of_accept 13 14 119 (accept_3_2 13 14 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 14 119 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 14 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 14 119
  (Polychromatic418967fa.accept_19_11_14_5_1_5629 11 14 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 14 119 (accept_3_2 10 14 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  14 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 14 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 14 119 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 14 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 14 119 7 1 2 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 14 119 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 14 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 119
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 14 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 14 119 (accept_3_2 4 14 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14
  119 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 14 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 14 119 (Polychromatic418967fa.accept_18_2_14_11_1_3139 2 14 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 119 (accept_3_2 1 14 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 119)))))))))))))) (allB_succ 13 119 (allA_of_3_0 13 13 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 12 119 (allA_succ_of_accept 11 12 119 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 12 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 119 (accept_3_2 10 12 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 12 119 (Polychromatic418967fa.accept_14_9_12_7_1_597 9
  12 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 119
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 12 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 12 119 (accept_3_2 7 12 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12
  119 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 12 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 12 119 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 12 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 119 (accept_3_2 4 12 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 12 119 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 12 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 12 119 (Polychromatic418967fa.accept_14_2_12_7_1_617 2
  12 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 119 (accept_3_2 1 12 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 119)))))))))))) (allB_succ 11 119 (allA_succ_of_accept 10 11 119
  (accept_3_2 10 11 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 119
  (Polychromatic418967fa.accept_13_9_11_2_1_1491 9 11 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 119 (Polychromatic418967fa.accept_10_8_1_9_1_413 8 11 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 119 (accept_3_2 7 11 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 119 (Polychromatic418967fa.accept_19_6_11_5_1_5628 6 11 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 119 (Polychromatic418967fa.accept_10_5_1_9_1_791 5
  11 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 119 (accept_3_2 4 11 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 119 (Polychromatic418967fa.accept_13_3_11_2_1_1422
  3 11 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 119
  (Polychromatic418967fa.accept_10_2_1_9_1_1248 2 11 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 119 (accept_3_2 1 11 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  119))))))))))) (allB_succ 10 119 (allA_of_3_0 10 10 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 119
  (allA_succ_of_accept 8 9 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 9 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 119 (accept_3_2 7 9 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 9 119 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 9 119 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 119 (Polychromatic418967fa.accept_13_5_9_2_1_1489 5
  9 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 119 (accept_3_2 4 9 119
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 119 (Polychromatic418967fa.accept_12_3_9_11_1_231 3
  9 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 119
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 9 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 119 (accept_3_2 1 9 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 119)))))))))
  (allB_succ 8 119 (allA_succ_of_accept 7 8 119 (accept_3_2 7 8 119 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 8 119 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 8 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 8 119 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 8 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 8 119 (accept_3_2 4 8 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 8 119 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 8 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 8 119
  (Polychromatic418967fa.accept_12_2_8_11_1_31 2 8 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 8 119 (accept_3_2 1 8 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 119))))))))
  (allB_succ 7 119 (allA_of_3_0 7 7 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 6 119 (allA_succ_of_accept 5
  6 119 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 6 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 119 (accept_3_2 4 6 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 6 119
  (Polychromatic418967fa.accept_9_3_6_2_1_160 3 6 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 6 119 (Polychromatic418967fa.accept_21_2_6_14_1_1569 2 6 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 119 (accept_3_2 1 6 119 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 6 119)))))) (allB_succ 5 119 (allA_succ_of_accept 4 5 119 (accept_3_2 4 5 119 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 119 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 5 119
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 119
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 5 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 119 (accept_3_2 1 5 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 119)))))
  (allB_succ 4 119 (allA_of_3_0 4 4 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 3 119 (allA_succ_of_accept 2
  3 119 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 3 119 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 119 (accept_3_2 1 3 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 119)))
  (allB_succ 2 119 (allA_succ_of_accept 1 2 119 (accept_3_2 1 2 119 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2
  119)) (allB_two
  119)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


