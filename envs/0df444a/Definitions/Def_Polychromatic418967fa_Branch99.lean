-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch99
-- name    : Polychromatic418967fa_Branch99
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:10:39.057195+00:00
-- url     : https://prove2.me/theorems/9d896ab3-0a94-4746-80a2-e34f2475f569
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

def Polychromatic418967fa.branch_99 : allB 99 99 :=
  allB_succ' 2 98 99 (Eq.refl Bool.true) (allA_succ_of_accept 1 98 99 (accept_3_4 1 98 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 98 99)) (allB_succ' 3 97 99 (Eq.refl Bool.true) (allA_succ_of_accept 2 97 99 (accept_3_5 2 97 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 97 99 (Polychromatic418967fa.accept_13_1_6_8_1_208 1
  97 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97 99))) (allB_succ' 4 96 99 (Eq.refl
  Bool.true) (allA_succ_of_gcd 3 96 99 3 1 32 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 2 96 99 (Polychromatic418967fa.accept_18_2_6_9_1_1032 2 96 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 99 (Polychromatic418967fa.accept_13_1_5_8_1_207 1
  96 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96 99)))) (allB_succ' 5 95 99 (Eq.refl
  Bool.true) (allA_succ_of_accept 4 95 99 (accept_3_4 4 95 99 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 95 99 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 95 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 95 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 99 (accept_3_4 1 95 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 95 99))))) (allB_succ' 6 94 99 (Eq.refl Bool.true) (allA_succ_of_accept 5 94
  99 (accept_3_5 5 94 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 94 99
  (Polychromatic418967fa.accept_7_4_3_1_1_87 4 94 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 94 99 (Polychromatic418967fa.accept_10_3_4_9_1_15 3 94 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 99 (accept_3_5 2 94 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 94 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 94 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94 99)))))) (allB_succ' 7 93 99 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 93 99 3 2 31 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 93 99 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 93 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 99 (Polychromatic418967fa.accept_10_4_3_9_1_1262 4 93 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 93 99 3 1 31 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 93 99
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 93 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 93 99 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 93 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 93 99))))))) (allB_succ' 8 92 99 (Eq.refl Bool.true) (allA_succ_of_accept 7
  92 99 (accept_3_4 7 92 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92 99
  (Polychromatic418967fa.accept_12_6_8_3_1_82 6 92 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 99 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 92 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 99 (accept_3_4 4 92 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 99 (Polychromatic418967fa.accept_18_3_2_9_1_1013 3 92 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 99 (Polychromatic418967fa.accept_14_2_8_1_1_1647 2
  92 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 99 (accept_3_4 1 92 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92 99)))))))) (allB_succ' 9 91 99 (Eq.refl Bool.true)
  (allA_succ_of_accept 8 91 99 (accept_3_5 8 91 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 99
  (Polychromatic418967fa.accept_15_7_1_9_1_1500 7 91 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 91 99 (Polychromatic418967fa.accept_14_6_7_1_1_78 6 91 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 99 (accept_3_5 5 91 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 91 99 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 91 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 99 (Polychromatic418967fa.accept_17_3_6_14_1_4312 3
  91 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 99 (accept_3_5 2 91 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 99 (Polychromatic418967fa.accept_19_1_15_4_1_4311 1
  91 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91 99))))))))) (allB_succ' 10 90 99
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 90 99 9 1 10 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 8 90 99 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 90 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 99
  (Polychromatic418967fa.accept_13_7_12_8_1_199 7 90 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 90 99 3 2 30 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 90 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 90 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 90 99 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 90 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 90 99 3 1 30 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 90 99
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 90 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 90 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 90 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 90 99)))))))))) (allB_succ' 11 89 99 (Eq.refl Bool.true) (allA_succ_of_accept 10 89 99
  (accept_3_4 10 89 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 89 99
  (Polychromatic418967fa.accept_12_9_5_3_1_782 9 89 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 89 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 89 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 99 (accept_3_4 7 89 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 89 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 89 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 99 (Polychromatic418967fa.accept_15_5_14_9_1_274 5
  89 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 89 99 (accept_3_4 4 89 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89 99 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 89
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 89 99
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 89 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 89 99 (accept_3_4 1 89 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 89 99)))))))))))
  (allB_succ' 12 88 99 (Eq.refl Bool.true) (allA_succ_of_gcd 11 88 99 11 1 8 9 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 88 99 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 88
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 88 99
  (Polychromatic418967fa.accept_20_9_8_19_1_802 9 88 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 88 99 (accept_3_5 8 88 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 88 99
  (Polychromatic418967fa.accept_6_1_4_3_1_14 7 88 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 88 99 (Polychromatic418967fa.accept_12_6_4_3_1_361 6 88 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 88 99 (accept_3_5 5 88 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 88 99 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 88 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 88 99 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 88
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 88 99 (accept_3_5 2 88 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 88 99 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 88
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88 99)))))))))))) (allB_succ' 13 87 99
  (Eq.refl Bool.true) (allA_succ_of_gcd 12 87 99 3 4 29 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 87 99 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 87 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 99
  (Polychromatic418967fa.accept_15_10_12_9_1_776 10 87 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 87 99 3 3 29 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 87 99 (Polychromatic418967fa.accept_10_8_7_9_1_425 8 87 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 99 (Polychromatic418967fa.accept_13_7_9_8_1_188 7 87 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 87 99 3 2 29 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 87 99
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 87 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 87 99 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 87 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 87 99 3 1 29 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 87 99 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 87 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 99
  (Polychromatic418967fa.accept_13_1_9_8_1_1734 1 87 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 87 99))))))))))))) (allB_succ' 14 86 99 (Eq.refl Bool.true) (allA_succ_of_accept 13 86 99 (accept_3_4 13 86
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 86 99
  (Polychromatic418967fa.accept_23_12_17_7_1_4310 12 86 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 86 99 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 86 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 99 (accept_3_4 10 86 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 86 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 86 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 99 (Polychromatic418967fa.accept_14_8_2_1_1_1652 8
  86 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 86 99 (accept_3_4 7 86 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86 99 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 86
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 86 99
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 86 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 86 99 (accept_3_4 4 86 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 86 99
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 86 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 86 99 (Polychromatic418967fa.accept_15_2_11_9_1_263 2 86 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 99 (accept_3_4 1 86 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 86 99)))))))))))))) (allB_succ' 15 85 99 (Eq.refl Bool.true) (allA_succ_of_accept 14 85 99
  (accept_3_5 14 85 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 99
  (Polychromatic418967fa.accept_19_13_9_4_1_4309 13 85 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 85 99 (Polychromatic418967fa.accept_13_12_7_8_1_1104 12 85 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 85 99 (accept_3_5 11 85 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 85 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 85 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 85 99 (Polychromatic418967fa.accept_12_9_1_3_1_350 9
  85 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 99 (accept_3_5 8 85 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 99 (Polychromatic418967fa.accept_21_7_1_15_1_680 7
  85 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 99
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 85 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 99 (accept_3_5 5 85 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85 99
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 85 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 85 99 (Polychromatic418967fa.accept_13_3_7_8_1_4192 3 85 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 99 (accept_3_5 2 85 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 99 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 85 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85 99))))))))))))))) (allB_succ' 16 84 99 (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 84 99 3 5 28 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 84 99 (Polychromatic418967fa.accept_13_1_6_8_1_208 14 84 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 99 (Polychromatic418967fa.accept_10_3_4_9_1_15 13 84 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 99 3 4 28 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 99
  (Polychromatic418967fa.accept_13_11_6_8_1_1121 11 84 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 84 99 (Polychromatic418967fa.accept_18_10_12_9_1_2012 10 84 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 84 99 3 3 28 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 84 99 (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 84 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 99
  (Polychromatic418967fa.accept_8_7_4_3_1_156 7 84 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 84 99 3 2 28 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 84 99 (Polychromatic418967fa.accept_10_5_4_9_1_420 5 84 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84 99 (Polychromatic418967fa.accept_18_4_12_9_1_2011 4 84 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 84 99 3 1 28 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 84 99
  (Polychromatic418967fa.accept_13_2_6_8_1_1092 2 84 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 84 99 (Polychromatic418967fa.accept_13_1_6_8_1_208 1 84 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 84 99)))))))))))))))) (allB_succ' 17 83 99 (Eq.refl Bool.true)
  (allA_succ_of_accept 16 83 99 (accept_3_4 16 83 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 83
  99 (Polychromatic418967fa.accept_18_15_11_9_1_4256 15 83 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 83 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 99 (accept_3_4 13 83 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 99 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 83 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 99
  (Polychromatic418967fa.accept_19_11_7_4_1_4308 11 83 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 99 (accept_3_4 10 83 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 83
  99 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 83 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 83 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 83 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 99 (accept_3_4 7 83 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 83 99 (Polychromatic418967fa.accept_10_6_3_9_1_1207 6 83 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 99 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 83
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 83 99 (accept_3_4 4 83 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83 99 (Polychromatic418967fa.accept_13_3_5_8_1_1099 3
  83 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 99
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 83 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 83 99 (accept_3_4 1 83 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 83
  99))))))))))))))))) (allB_succ' 18 82 99 (Eq.refl Bool.true) (allA_succ_of_accept 17 82 99 (accept_3_5 17 82 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 82 99 (Polychromatic418967fa.accept_15_1_7_9_1_20 16
  82 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 82 99
  (Polychromatic418967fa.accept_16_15_2_3_1_4262 15 82 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 82 99 (accept_3_5 14 82 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 82
  99 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 82 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 82 99 (Polychromatic418967fa.accept_13_12_4_8_1_1120 12 82 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 82 99 (accept_3_5 11 82 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 82 99 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 82 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 82 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 82
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 82 99 (accept_3_5 8 82 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 82 99 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 82
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 82 99
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 82 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 82 99 (accept_3_5 5 82 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 82 99
  (Polychromatic418967fa.accept_7_4_5_1_1_418 4 82 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 82 99 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 82 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 99 (accept_3_5 2 82 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 82 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 82 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82 99)))))))))))))))))) (allB_succ' 19 81 99 (Eq.refl Bool.true)
  (allA_succ_of_gcd 18 81 99 9 2 9 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 81 99 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 81 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 99 (Polychromatic418967fa.accept_15_1_6_9_1_254 16 81 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 81 99 3 5 27 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 81 99
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 81 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 99 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 81 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 81 99 3 4 27 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 81 99 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 81 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 99
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 81 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 81 99 9 1 9 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 81 99 (Polychromatic418967fa.accept_10_8_1_9_1_413 8 81 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 99 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 81 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 81 99 3 2 27 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 81 99
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 81 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 99 (Polychromatic418967fa.accept_14_4_11_1_1_940 4 81 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 81 99 3 1 27 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 81 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 81 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 99
  (Polychromatic418967fa.accept_12_1_9_3_1_370 1 81 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 81 99))))))))))))))))))) (allB_succ' 20 80 99 (Eq.refl Bool.true) (allA_succ_of_accept 19 80 99 (accept_3_4
  19 80 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 80 99
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 80 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 80 99 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 80 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 99 (accept_3_4 16 80 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 80 99 (Polychromatic418967fa.accept_17_15_12_14_1_2087 15 80 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 80 99
  (Polychromatic418967fa.accept_15_14_5_9_1_2284 14 80 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 80 99 (accept_3_4 13 80 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 80
  99 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 80 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 80 99 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 80 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 80 99 (accept_3_4 10 80 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 80 99 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 80 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 99 (Polychromatic418967fa.accept_21_8_17_15_1_2834
  8 80 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 80 99 (accept_3_4 7 80 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80 99 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 80
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 80 99
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 80 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 80 99 (accept_3_4 4 80 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 80 99
  (Polychromatic418967fa.accept_15_3_5_9_1_764 3 80 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 80 99 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 80 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 80 99 (accept_3_4 1 80 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 80 99)))))))))))))))))))) (allB_succ' 21 79 99 (Eq.refl Bool.true) (allA_succ_of_accept 20 79 99
  (accept_3_5 20 79 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 99
  (Polychromatic418967fa.accept_13_6_1_8_1_1116 19 79 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 79 99 (Polychromatic418967fa.accept_13_5_1_8_1_1115 18 79 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 99 (accept_3_5 17 79 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 79 99 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 79 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 99 (Polychromatic418967fa.accept_23_15_10_7_1_4307
  15 79 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 99 (accept_3_5 14 79
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 99 (Polychromatic418967fa.accept_7_6_2_1_1_214
  13 79 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 99
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 79 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 99 (accept_3_5 11 79 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 79
  99 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 79 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 79 99 (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 79 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 99 (accept_3_5 8 79 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 79 99 (Polychromatic418967fa.accept_13_7_1_8_1_1778 7 79 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 99 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 79
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 99 (accept_3_5 5 79 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79 99 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 79
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 99
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 79 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 79 99 (accept_3_5 2 79 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79 99
  (Polychromatic418967fa.accept_19_1_3_4_1_4306 1 79 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 79 99))))))))))))))))))))) (allB_succ' 22 78 99 (Eq.refl Bool.true) (allA_succ_of_gcd 21 78 99 3 7 26 33
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 78 99
  (Polychromatic418967fa.accept_12_8_6_3_1_366 20 78 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 78 99 (Polychromatic418967fa.accept_18_1_6_9_1_2001 19 78 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 99 3 6 26 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 78 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 78 99
  (Polychromatic418967fa.accept_12_4_6_3_1_332 16 78 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 78 99 3 5 26 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 78 99 (Polychromatic418967fa.accept_10_4_8_9_1_784 14 78 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 78 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 99 3 4 26 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 99
  (Polychromatic418967fa.accept_10_1_8_9_1_787 11 78 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 78 99 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 78 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 78 99 3 3 26 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 78 99 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 78 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 99
  (Polychromatic418967fa.accept_10_7_8_9_1_785 7 78 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 78 99 3 2 26 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 78 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 78 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 78 99 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 78 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 78 99 3 1 26 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 78 99
  (Polychromatic418967fa.accept_12_2_6_3_1_331 2 78 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 78 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 78 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 78 99)))))))))))))))))))))) (allB_succ' 23 77 99 (Eq.refl Bool.true) (allA_succ_of_gcd
  22 77 99 11 2 7 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  21 77 99 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 77 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 77 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 99 (accept_3_4 19 77 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 77 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 99
  (Polychromatic418967fa.accept_13_4_12_8_1_197 17 77 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 99 (accept_3_4 16 77 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 77
  99 (Polychromatic418967fa.accept_16_15_13_3_1_4215 15 77 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 77 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 99 (accept_3_4 13 77 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 99 (Polychromatic418967fa.accept_10_2_7_9_1_783 12 77 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 77 99 11 1 7 9 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 77 99 (accept_3_4 10 77 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 77 99 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 77 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 77 99
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 77 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 77 99 (accept_3_4 7 77 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 99
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 77 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 77 99 (Polychromatic418967fa.accept_13_5_12_8_1_198 5 77 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 77 99 (accept_3_4 4 77 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 77 99 (Polychromatic418967fa.accept_19_3_1_4_1_1860 3 77 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 77 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 77
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 99 (accept_3_4 1 77 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 77 99))))))))))))))))))))))) (allB_succ' 24 76 99 (Eq.refl
  Bool.true) (allA_succ_of_accept 23 76 99 (accept_3_5 23 76 99 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 76 99 (Polychromatic418967fa.accept_13_9_11_8_1_195 22 76 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 76 99 (Polychromatic418967fa.accept_14_7_6_1_1_1656 21 76 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 76 99 (accept_3_5 20 76 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 76 99 (Polychromatic418967fa.accept_6_1_4_3_1_14 19
  76 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 76 99
  (Polychromatic418967fa.accept_12_6_4_3_1_361 18 76 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 76 99 (accept_3_5 17 76 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 76
  99 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 76 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 76 99 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 76 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 76 99 (accept_3_5 14 76 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 76 99 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 76 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 76 99 (Polychromatic418967fa.accept_7_5_6_1_1_407 12
  76 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 76 99 (accept_3_5 11 76 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 76 99 (Polychromatic418967fa.accept_13_10_11_8_1_1770
  10 76 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 76 99
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 76 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 76 99 (accept_3_5 8 76 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 76 99
  (Polychromatic418967fa.accept_6_1_4_3_1_14 7 76 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 76 99 (Polychromatic418967fa.accept_12_6_4_3_1_361 6 76 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 76 99 (accept_3_5 5 76 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 76 99 (Polychromatic418967fa.accept_13_4_11_8_1_1768 4 76 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 76 99 (Polychromatic418967fa.accept_10_3_6_9_1_779 3
  76 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 99 (accept_3_5 2 76 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 76 99 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 76
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76 99)))))))))))))))))))))))) (allB_succ' 25
  75 99 (Eq.refl Bool.true) (allA_succ_of_gcd 24 75 99 3 8 25 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 75 99 (Polychromatic418967fa.accept_16_7_11_3_1_1330 23 75 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 99
  (Polychromatic418967fa.accept_16_6_11_3_1_2198 22 75 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 75 99 3 7 25 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 75 99 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 75 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 99 (Polychromatic418967fa.accept_18_1_3_9_1_328 19 75 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 75 99 3 6 25 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 75 99
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 75 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 75 99 (Polychromatic418967fa.accept_10_6_5_9_1_1233 16 75 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 99 3 5 25 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 99 (Polychromatic418967fa.accept_10_4_5_9_1_1231 14 75 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 99
  (Polychromatic418967fa.accept_7_6_5_1_1_416 13 75 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 75 99 3 4 25 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 75 99 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 75 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 99 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 75 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 75 99 3 3 25 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 75 99
  (Polychromatic418967fa.accept_16_8_11_3_1_4279 8 75 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 99 (Polychromatic418967fa.accept_13_7_10_8_1_567 7 75 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 75 99 3 2 25 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 75 99 (Polychromatic418967fa.accept_13_5_10_8_1_1127 5 75 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 99
  (Polychromatic418967fa.accept_7_4_5_1_1_418 4 75 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 75 99 3 1 25 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 75 99 (Polychromatic418967fa.accept_13_2_10_8_1_1126 2 75 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 99 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 75 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75 99))))))))))))))))))))))))) (allB_succ' 26
  74 99 (Eq.refl Bool.true) (allA_succ_of_accept 25 74 99 (accept_3_4 25 74 99 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 74 99 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 74 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 74 99 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 74 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 99 (accept_3_4 22 74 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 74 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 74
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 99
  (Polychromatic418967fa.accept_13_7_9_8_1_188 20 74 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 74 99 (accept_3_4 19 74 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 74
  99 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 74 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 74 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 74 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 99 (accept_3_4 16 74 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 74 99 (Polychromatic418967fa.accept_10_5_4_9_1_420 15 74 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 99 (Polychromatic418967fa.accept_13_1_9_8_1_1734
  14 74 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 74 99 (accept_3_4 13 74
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 74 99 (Polychromatic418967fa.accept_7_5_4_1_1_412
  12 74 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 74 99
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 74 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 74 99 (accept_3_4 10 74 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 74
  99 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 74 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 74 99 (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 74 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 74 99 (accept_3_4 7 74 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 74 99 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 74 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 74 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 74
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 99 (accept_3_4 4 74 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 74 99 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 74
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 99
  (Polychromatic418967fa.accept_19_2_17_4_1_1856 2 74 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 74 99 (accept_3_4 1 74 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  99)))))))))))))))))))))))))) (allB_succ' 27 73 99 (Eq.refl Bool.true) (allA_succ_of_accept 26 73 99 (accept_3_5 26 73
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 99 (Polychromatic418967fa.accept_7_4_3_1_1_87
  25 73 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 99
  (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 73 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 99 (accept_3_5 23 73 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 73
  99 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 73 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 73 99 (Polychromatic418967fa.accept_12_9_1_3_1_350 21 73 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 99 (accept_3_5 20 73 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 73 99 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 73 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 18
  73 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 73 99 (accept_3_5 17 73 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 73 99 (Polychromatic418967fa.accept_6_4_1_3_1_77 16
  73 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 73 99
  (Polychromatic418967fa.accept_22_15_7_11_1_4305 15 73 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 73 99 (accept_3_5 14 73 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 73
  99 (Polychromatic418967fa.accept_25_13_23_24_1_4304 13 73 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 73 99 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 73 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 73 99 (accept_3_5 11 73 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 73 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 73 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 73 99
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 73 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 73 99 (accept_3_5 8 73 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 99
  (Polychromatic418967fa.accept_15_7_13_9_1_1466 7 73 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 73 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 73 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 73 99 (accept_3_5 5 73 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 73 99 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 73 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 73 99 (Polychromatic418967fa.accept_15_3_13_9_1_3196 3
  73 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 99 (accept_3_5 2 73 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 99 (Polychromatic418967fa.accept_19_1_16_4_1_4303 1
  73 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73 99)))))))))))))))))))))))))))
  (allB_succ' 28 72 99 (Eq.refl Bool.true) (allA_succ_of_gcd 27 72 99 9 3 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 72 99 (Polychromatic418967fa.accept_17_9_4_14_1_4302
  26 72 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 99
  (Polychromatic418967fa.accept_13_12_7_8_1_1104 25 72 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 72 99 3 8 24 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 72 99 (Polychromatic418967fa.accept_13_10_7_8_1_1794 23 72 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 72 99 (Polychromatic418967fa.accept_13_9_7_8_1_1122 22 72 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 72 99 3 7 24 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 72 99
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 72 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 72 99 (Polychromatic418967fa.accept_15_4_12_9_1_773 19 72 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72 99 9 2 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 72 99 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 72 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 72 99
  (Polychromatic418967fa.accept_13_3_7_8_1_4192 16 72 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 72 99 3 5 24 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 72 99 (Polychromatic418967fa.accept_13_1_7_8_1_1796 14 72 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 99 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 72 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 99 3 4 24 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 99
  (Polychromatic418967fa.accept_10_1_2_9_1_152 11 72 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 72 99 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 72 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 72 99 9 1 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 72 99 (Polychromatic418967fa.accept_14_8_2_1_1_1652 8 72 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 99
  (Polychromatic418967fa.accept_10_7_2_9_1_775 7 72 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 72 99 3 2 24 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 72 99 (Polychromatic418967fa.accept_15_5_12_9_1_2253 5 72 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 72 99 (Polychromatic418967fa.accept_15_4_12_9_1_773 4 72 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 72 99 3 1 24 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 72 99
  (Polychromatic418967fa.accept_13_2_7_8_1_4221 2 72 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 72 99 (Polychromatic418967fa.accept_10_1_2_9_1_152 1 72 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 72 99)))))))))))))))))))))))))))) (allB_succ' 29 71 99 (Eq.refl Bool.true)
  (allA_succ_of_accept 28 71 99 (accept_3_4 28 71 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 71
  99 (Polychromatic418967fa.accept_13_1_6_8_1_208 27 71 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 71 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 71 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 99 (accept_3_4 25 71 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 71 99 (Polychromatic418967fa.accept_13_11_6_8_1_1121 24 71 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 99 (Polychromatic418967fa.accept_17_6_3_14_1_2078
  23 71 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 71 99 (accept_3_4 22 71
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 71 99
  (Polychromatic418967fa.accept_12_9_11_3_1_772 21 71 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 71 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 71 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 99 (accept_3_4 19 71 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 71 99 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 71 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 99 (Polychromatic418967fa.accept_15_2_11_9_1_263
  17 71 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 71 99 (accept_3_4 16 71
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 71 99 (Polychromatic418967fa.accept_10_5_1_9_1_791
  15 71 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 71 99
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 71 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 71 99 (accept_3_4 13 71 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 71
  99 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 71 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 71 99 (Polychromatic418967fa.accept_13_11_6_8_1_1121 11 71 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 71 99 (accept_3_4 10 71 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 71 99 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 71 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 71
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 99 (accept_3_4 7 71 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 99 (Polychromatic418967fa.accept_15_6_11_9_1_3215 6
  71 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 99
  (Polychromatic418967fa.accept_10_5_1_9_1_791 5 71 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 99 (accept_3_4 4 71 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71 99
  (Polychromatic418967fa.accept_21_3_8_15_1_4301 3 71 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 71 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 99 (accept_3_4 1 71 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 99))))))))))))))))))))))))))))) (allB_succ' 30 70 99 (Eq.refl Bool.true) (allA_succ_of_accept
  29 70 99 (accept_3_5 29 70 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 70 99
  (Polychromatic418967fa.accept_19_9_13_4_1_2982 28 70 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 70 99 (Polychromatic418967fa.accept_13_1_5_8_1_207 27 70 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 70 99 (accept_3_5 26 70 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 70 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 70 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 70 99 (Polychromatic418967fa.accept_21_3_7_15_1_4300
  24 70 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 70 99 (accept_3_5 23 70
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 70 99
  (Polychromatic418967fa.accept_17_5_2_14_1_4270 22 70 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 70 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 70 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 70 99 (accept_3_5 20 70 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 70 99 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 70 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 70 99 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  18 70 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 70 99 (accept_3_5 17 70
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 70 99
  (Polychromatic418967fa.accept_13_3_5_8_1_1099 16 70 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 70 99 (Polychromatic418967fa.accept_18_15_16_9_1_4299 15 70 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 70 99 (accept_3_5 14 70 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 70 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 70 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 70 99 (Polychromatic418967fa.accept_13_12_5_8_1_1101
  12 70 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 70 99 (accept_3_5 11 70
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 70 99
  (Polychromatic418967fa.accept_13_10_5_8_1_2555 10 70 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 70 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 70 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 8 70 99 (accept_3_5 8 70 99 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 70 99 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 70 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 70 99 (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 70 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 70 99 (accept_3_5 5 70 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 70 99 (Polychromatic418967fa.accept_15_4_10_9_1_4298 4 70 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 70 99
  (Polychromatic418967fa.accept_13_3_5_8_1_1099 3 70 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 70 99 (accept_3_5 2 70 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 70 99
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 70 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 70 99)))))))))))))))))))))))))))))) (allB_succ' 31 69 99 (Eq.refl Bool.true) (allA_succ_of_gcd 30 69 99 3 10
  23 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 69 99
  (Polychromatic418967fa.accept_12_5_9_3_1_85 29 69 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 69 99 (Polychromatic418967fa.accept_18_10_15_9_1_1054 28 69 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 69 99 3 9 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 69 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 69 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 99
  (Polychromatic418967fa.accept_12_1_9_3_1_370 25 69 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 69 99 3 8 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 69 99 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 69 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 69 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 69 99 3 7 23 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 69 99
  (Polychromatic418967fa.accept_19_1_12_4_1_4263 20 69 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 99 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 69 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 69 99 3 6 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 69 99 (Polychromatic418967fa.accept_12_5_9_3_1_85 17 69 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 99
  (Polychromatic418967fa.accept_7_2_6_1_1_73 16 69 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 69 99 3 5 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 69 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 69 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 99 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 69 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 69 99 3 4 23 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 69 99
  (Polychromatic418967fa.accept_12_11_9_3_1_792 11 69 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 69 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 69 99 3 3 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 69 99 (Polychromatic418967fa.accept_16_8_5_3_1_4297 8 69 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 99
  (Polychromatic418967fa.accept_12_7_9_3_1_767 7 69 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 69 99 3 2 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 69 99 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 69 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 99 (Polychromatic418967fa.accept_17_4_1_14_1_4296 4 69 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 69 99 3 1 23 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 99
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 69 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 69 99 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 69 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 69 99))))))))))))))))))))))))))))))) (allB_succ' 32 68 99 (Eq.refl
  Bool.true) (allA_succ_of_accept 31 68 99 (accept_3_4 31 68 99 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 68 99 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 68 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 68 99 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 68 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 99 (accept_3_4 28 68 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 68 99 (Polychromatic418967fa.accept_7_6_5_1_1_416 27
  68 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 99
  (Polychromatic418967fa.accept_19_7_11_4_1_1872 26 68 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 68 99 (accept_3_4 25 68 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 68
  99 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 68 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 68 99 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 68 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 99 (accept_3_4 22 68 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 68 99 (Polychromatic418967fa.accept_10_1_8_9_1_787 21 68 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 99 (Polychromatic418967fa.accept_7_6_5_1_1_416 20
  68 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 68 99 (accept_3_4 19 68 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 68 99 (Polychromatic418967fa.accept_7_4_5_1_1_418 18
  68 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 68 99
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 68 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 68 99 (accept_3_4 16 68 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 68
  99 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 68 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 68 99 (Polychromatic418967fa.accept_10_4_8_9_1_784 14 68 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 68 99 (accept_3_4 13 68 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 68 99 (Polychromatic418967fa.accept_16_12_4_3_1_4295 12 68 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 68 99 (Polychromatic418967fa.accept_6_5_2_3_1_81 11
  68 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 99 (accept_3_4 10 68 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 68 99 (Polychromatic418967fa.accept_13_9_3_8_1_573 9
  68 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 99
  (Polychromatic418967fa.accept_16_8_4_3_1_3146 8 68 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 68 99 (accept_3_4 7 68 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68 99
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 68 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 68 99 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 68 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 99 (accept_3_4 4 68 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 68 99 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 68 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 99 (Polychromatic418967fa.accept_15_2_8_9_1_4294 2
  68 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 99 (accept_3_4 1 68 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68 99)))))))))))))))))))))))))))))))) (allB_succ' 33 67 99 (Eq.refl
  Bool.true) (allA_succ_of_accept 32 67 99 (accept_3_5 32 67 99 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 67 99 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 67 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 99 (Polychromatic418967fa.accept_20_10_7_19_1_4293 30 67 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 67 99 (accept_3_5 29 67 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 67 99 (Polychromatic418967fa.accept_6_4_1_3_1_77 28
  67 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 67 99
  (Polychromatic418967fa.accept_19_8_10_4_1_4292 27 67 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 67 99 (accept_3_5 26 67 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 67
  99 (Polychromatic418967fa.accept_17_8_16_14_1_4261 25 67 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 67 99 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 67 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 67 99 (accept_3_5 23 67 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 67 99 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 67 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 67 99
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 67 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 67 99 (accept_3_5 20 67 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 67
  99 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 67 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 67 99 (Polychromatic418967fa.accept_10_8_7_9_1_425 18 67 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 67 99 (accept_3_5 17 67 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 67 99 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 67 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 67 99
  (Polychromatic418967fa.accept_17_15_16_14_1_4291 15 67 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 67 99 (accept_3_5 14 67 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 67
  99 (Polychromatic418967fa.accept_15_13_7_9_1_3210 13 67 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 67 99 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 67 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 67 99 (accept_3_5 11 67 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 67 99 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 67 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 67 99
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 67 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 67 99 (accept_3_5 8 67 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 99
  (Polychromatic418967fa.accept_13_7_2_8_1_1746 7 67 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 67 99 (Polychromatic418967fa.accept_13_6_2_8_1_1782 6 67 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 67 99 (accept_3_5 5 67 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 67 99 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 67 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 67 99 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 67
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 99 (accept_3_5 2 67 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 99 (Polychromatic418967fa.accept_15_1_7_9_1_20 1 67
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67 99)))))))))))))))))))))))))))))))))
  (allB_succ' 34 66 99 (Eq.refl Bool.true) (allA_succ_of_gcd 33 66 99 33 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 66 99 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 66
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 99
  (Polychromatic418967fa.accept_13_5_1_8_1_1115 31 66 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 66 99 3 10 22 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 66 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 66 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 66 99 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 66 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 66 99 3 9 22 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 66 99
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 66 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 66 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 66 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 99 3 8 22 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 99 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 66 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 99 11 2 6 9 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 66 99 3 7 22 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 66 99
  (Polychromatic418967fa.accept_12_8_6_3_1_366 20 66 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 66 99 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 66 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 99 3 6 22 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 66 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 66 99
  (Polychromatic418967fa.accept_7_2_3_1_1_10 16 66 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 66 99 3 5 22 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 66 99 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 66 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 66 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 99 3 4 22 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 66 99 11 1 6 9 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 66 99
  (Polychromatic418967fa.accept_12_10_6_3_1_786 10 66 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 66 99 3 3 22 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 66 99 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 66 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 99 (Polychromatic418967fa.accept_13_7_1_8_1_1778 7 66 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 99 3 2 22 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 99
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 66 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 66 99 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 66 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 66 99 3 1 22 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 66 99 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 66 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 99
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 66 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 66 99)))))))))))))))))))))))))))))))))) (allB_succ' 35 65 99 (Eq.refl Bool.true) (allA_succ_of_accept 34 65
  99 (accept_3_4 34 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 99
  (Polychromatic418967fa.accept_12_9_5_3_1_782 33 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 65 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 65 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 99 (accept_3_4 31 65 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 65 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 65 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 99 (Polychromatic418967fa.accept_15_14_5_9_1_2284
  29 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 99 (accept_3_4 28 65
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 99 (Polychromatic418967fa.accept_7_6_2_1_1_214
  27 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 65 99
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 65 99 (accept_3_4 25 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 65
  99 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 65 99 (Polychromatic418967fa.accept_22_1_21_11_1_4290 23 65 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 99 (accept_3_4 22 65 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 65 99 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 65 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 65 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 20
  65 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 99 (accept_3_4 19 65 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 18
  65 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 99
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 99 (accept_3_4 16 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 65
  99 (Polychromatic418967fa.accept_18_15_11_9_1_4256 15 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 65 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 99 (accept_3_4 13 65 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 99 (Polychromatic418967fa.accept_15_12_5_9_1_3234 12 65 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 99
  (Polychromatic418967fa.accept_10_1_5_9_1_157 11 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 99 (accept_3_4 10 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 65
  99 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 65 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 65 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 99 (accept_3_4 7 65 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 65 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 65 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 99 (Polychromatic418967fa.accept_19_5_8_4_1_4289 5
  65 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 65 99 (accept_3_4 4 65 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65 99 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 65
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 99
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 65 99 (accept_3_4 1 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65
  99))))))))))))))))))))))))))))))))))) (allB_succ' 36 64 99 (Eq.refl Bool.true) (allA_succ_of_accept 35 64 99
  (accept_3_5 35 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 64 99
  (Polychromatic418967fa.accept_20_14_4_19_1_4288 34 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 64 99 (Polychromatic418967fa.accept_10_3_4_9_1_15 33 64 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 64 99 (accept_3_5 32 64 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 64 99 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 64 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 64 99 (Polychromatic418967fa.accept_12_6_4_3_1_361 30
  64 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 64 99 (accept_3_5 29 64 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 64 99 (Polychromatic418967fa.accept_10_8_4_9_1_1229
  28 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 64 99
  (Polychromatic418967fa.accept_13_1_12_8_1_1818 27 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 64 99 (accept_3_5 26 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 64
  99 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 64 99 (Polychromatic418967fa.accept_21_3_1_15_1_4287 24 64 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 64 99 (accept_3_5 23 64 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 64 99 (Polychromatic418967fa.accept_13_9_12_8_1_570 22 64 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 64 99 (Polychromatic418967fa.accept_14_7_8_1_1_1621
  21 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 64 99 (accept_3_5 20 64
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 64 99 (Polychromatic418967fa.accept_6_1_4_3_1_14
  19 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 64 99
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 64 99 (accept_3_5 17 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 64
  99 (Polychromatic418967fa.accept_14_2_8_1_1_1647 16 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 64 99 (Polychromatic418967fa.accept_10_5_4_9_1_420 15 64 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 64 99 (accept_3_5 14 64 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 64 99 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 64 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 64 99 (Polychromatic418967fa.accept_15_12_4_9_1_3204
  12 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 64 99 (accept_3_5 11 64
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 64 99
  (Polychromatic418967fa.accept_13_10_12_8_1_2550 10 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 64 99 (Polychromatic418967fa.accept_13_9_12_8_1_570 9 64 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 64 99 (accept_3_5 8 64 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 64 99 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 64 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 64 99 (Polychromatic418967fa.accept_12_6_4_3_1_361 6
  64 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 64 99 (accept_3_5 5 64 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 64 99 (Polychromatic418967fa.accept_13_4_12_8_1_197 4
  64 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 64 99
  (Polychromatic418967fa.accept_10_3_4_9_1_15 3 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 64 99 (accept_3_5 2 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 64 99
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 64 99)))))))))))))))))))))))))))))))))))) (allB_succ' 37 63 99 (Eq.refl Bool.true) (allA_succ_of_gcd 36 63
  99 9 4 7 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 63
  99 (Polychromatic418967fa.accept_13_9_11_8_1_195 35 63 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 63 99 (Polychromatic418967fa.accept_10_4_3_9_1_1262 34 63 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 63 99 3 11 21 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 63 99 (Polychromatic418967fa.accept_13_6_11_8_1_1111 32 63 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 99
  (Polychromatic418967fa.accept_19_12_6_4_1_2992 31 63 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 63 99 3 10 21 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 63 99 (Polychromatic418967fa.accept_13_3_11_8_1_1094 29 63 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 99 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 63 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 63 99 9 3 7 11 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 63 99
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 26 63 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 99 (Polychromatic418967fa.accept_15_10_3_9_1_3285 25 63 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 63 99 3 8 21 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 63 99 (Polychromatic418967fa.accept_13_10_11_8_1_1770 23 63 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 99
  (Polychromatic418967fa.accept_13_9_11_8_1_195 22 63 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 63 99 3 7 21 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 63 99 (Polychromatic418967fa.accept_8_4_7_3_1_144 20 63 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 99 (Polychromatic418967fa.accept_13_6_11_8_1_1111 19 63 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 63 99 9 2 7 11 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 63 99
  (Polychromatic418967fa.accept_13_4_11_8_1_1768 17 63 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 63 99 (Polychromatic418967fa.accept_10_6_3_9_1_1207 16 63 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 63 99 3 5 21 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 63 99 (Polychromatic418967fa.accept_10_4_3_9_1_1262 14 63 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 99
  (Polychromatic418967fa.accept_14_13_7_1_1_1618 13 63 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 63 99 3 4 21 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 63 99 (Polychromatic418967fa.accept_16_11_15_3_1_1304 11 63 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 99 (Polychromatic418967fa.accept_13_10_11_8_1_1770 10 63 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 63 99 9 1 7 11 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 63 99
  (Polychromatic418967fa.accept_14_8_7_1_1_1615 8 63 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 99 (Polychromatic418967fa.accept_16_7_15_3_1_1302 7 63 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 63 99 3 2 21 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 63 99 (Polychromatic418967fa.accept_15_5_3_9_1_283 5 63 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 99
  (Polychromatic418967fa.accept_8_4_7_3_1_144 4 63 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 63 99 3 1 21 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 63 99 (Polychromatic418967fa.accept_16_2_15_3_1_1300 2 63 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 99 (Polychromatic418967fa.accept_13_1_11_8_1_2562 1 63 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63 99)))))))))))))))))))))))))))))))))))))
  (allB_succ' 38 62 99 (Eq.refl Bool.true) (allA_succ_of_accept 37 62 99 (accept_3_4 37 62 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 62 99 (Polychromatic418967fa.accept_23_13_16_7_1_2722 36 62 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 62 99
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 62 99 (accept_3_4 34 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 62
  99 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 62 99 (Polychromatic418967fa.accept_20_12_2_19_1_4286 32 62 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 62 99 (accept_3_4 31 62 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 62 99 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 62 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 62 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 62
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 62 99 (accept_3_4 28 62 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 62 99 (Polychromatic418967fa.accept_10_7_2_9_1_775 27
  62 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 62 99
  (Polychromatic418967fa.accept_7_5_6_1_1_407 26 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 62 99 (accept_3_4 25 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 62
  99 (Polychromatic418967fa.accept_13_11_10_8_1_1804 24 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 62 99 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 62 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 62 99 (accept_3_4 22 62 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 62 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 62 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 62 99
  (Polychromatic418967fa.accept_13_7_10_8_1_567 20 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 62 99 (accept_3_4 19 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 62
  99 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 62 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 62 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 62 99 (accept_3_4 16 62 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 62 99 (Polychromatic418967fa.accept_13_2_10_8_1_1126 15 62 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 62 99
  (Polychromatic418967fa.accept_21_14_20_15_1_4285 14 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 62 99 (accept_3_4 13 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 62
  99 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 62 99 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 62 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 62 99 (accept_3_4 10 62 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 62 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 62 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 62 99 (Polychromatic418967fa.accept_15_8_2_9_1_3200 8
  62 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 62 99 (accept_3_4 7 62 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 62 99 (Polychromatic418967fa.accept_12_6_2_3_1_354 6
  62 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 62 99
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 62 99 (accept_3_4 4 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 62 99
  (Polychromatic418967fa.accept_17_3_11_14_1_2071 3 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 62 99 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 62 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 99 (accept_3_4 1 62 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 62 99)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 61 99 (Eq.refl Bool.true)
  (allA_succ_of_accept 38 61 99 (accept_3_5 38 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 61
  99 (Polychromatic418967fa.accept_13_11_9_8_1_1125 37 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 61 99 (Polychromatic418967fa.accept_15_6_1_9_1_1476 36 61 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 61 99 (accept_3_5 35 61 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 61 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 61 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 61 99
  (Polychromatic418967fa.accept_12_9_1_3_1_350 33 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 61 99 (accept_3_5 32 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 61
  99 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 61 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 61 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 61 99 (accept_3_5 29 61 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 61 99 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 61 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 61 99 (Polychromatic418967fa.accept_7_6_5_1_1_416 27
  61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 99 (accept_3_5 26 61 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 99 (Polychromatic418967fa.accept_7_4_5_1_1_418 25
  61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 99
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 99 (accept_3_5 23 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 61
  99 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 61 99 (Polychromatic418967fa.accept_12_9_1_3_1_350 21 61 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 99 (accept_3_5 20 61 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 61 99 (Polychromatic418967fa.accept_27_19_7_18_1_4284 19 61 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 18
  61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 61 99 (accept_3_5 17 61 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 61 99 (Polychromatic418967fa.accept_6_4_1_3_1_77 16
  61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 61 99
  (Polychromatic418967fa.accept_10_5_1_9_1_791 15 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 61 99 (accept_3_5 14 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 61
  99 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 61 99 (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 61 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 61 99 (accept_3_5 11 61 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 61 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 61 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 61 99 (Polychromatic418967fa.accept_12_9_1_3_1_350 9
  61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 99 (accept_3_5 8 61 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 99 (Polychromatic418967fa.accept_13_7_9_8_1_188 7
  61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 99
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 99 (accept_3_5 5 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61 99
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 99 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 61 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 99 (accept_3_5 2 61 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 99 (Polychromatic418967fa.accept_13_1_9_8_1_1734 1 61 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 99))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 60 99
  (Eq.refl Bool.true) (allA_succ_of_gcd 39 60 99 3 13 20 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 38 60 99 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 60 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 99
  (Polychromatic418967fa.accept_18_1_6_9_1_2001 37 60 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 60 99 3 12 20 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 60 99 (Polychromatic418967fa.accept_19_16_3_4_1_4281 35 60 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 60 99 (Polychromatic418967fa.accept_21_13_18_15_1_2837 34 60
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 60 99 3 11 20 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 60 99
  (Polychromatic418967fa.accept_18_14_6_9_1_1950 32 60 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 60 99 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 60 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 99 3 10 20 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 99 (Polychromatic418967fa.accept_17_12_9_14_1_4283 29 60 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 60 99
  (Polychromatic418967fa.accept_21_7_18_15_1_2887 28 60 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 60 99 3 9 20 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 60 99 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 60 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 99 (Polychromatic418967fa.accept_14_11_4_1_1_4255 25 60 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 99 3 8 20 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 99
  (Polychromatic418967fa.accept_8_7_4_3_1_156 23 60 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 60 99 (Polychromatic418967fa.accept_17_5_9_14_1_4282 22 60 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 60 99 3 7 20 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 60 99 (Polychromatic418967fa.accept_16_4_12_3_1_2180 20 60 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 99
  (Polychromatic418967fa.accept_7_5_4_1_1_412 19 60 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 60 99 3 6 20 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 60 99 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 60 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 60 99 (Polychromatic418967fa.accept_19_16_3_4_1_4281 16 60 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 60 99 3 5 20 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 60 99
  (Polychromatic418967fa.accept_18_14_6_9_1_1950 14 60 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 60 99 (Polychromatic418967fa.accept_18_13_6_9_1_4280 13 60 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 99 3 4 20 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 99 (Polychromatic418967fa.accept_14_11_4_1_1_4255 11 60 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 60 99
  (Polychromatic418967fa.accept_7_3_4_1_1_71 10 60 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 60 99 3 3 20 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 60 99 (Polychromatic418967fa.accept_16_8_12_3_1_4194 8 60 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 99 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 60 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 99 3 2 20 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 99
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 60 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 60 99 (Polychromatic418967fa.accept_16_4_12_3_1_2180 4 60 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 60 99 3 1 20 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 60 99 (Polychromatic418967fa.accept_18_2_6_9_1_1032 2 60 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 99
  (Polychromatic418967fa.accept_18_1_6_9_1_2001 1 60 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 60 99)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 59 99 (Eq.refl Bool.true) (allA_succ_of_accept
  40 59 99 (accept_3_4 40 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 59 99
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 59 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 59 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 99 (accept_3_4 37 59 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 59 99 (Polychromatic418967fa.accept_13_10_7_8_1_1794 36 59 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 99 (Polychromatic418967fa.accept_13_9_7_8_1_1122
  35 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 59 99 (accept_3_4 34 59
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 59 99 (Polychromatic418967fa.accept_7_5_3_1_1_424
  33 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 59 99
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 59 99 (accept_3_4 31 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 59
  99 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 59 99 (Polychromatic418967fa.accept_13_3_7_8_1_4192 29 59 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 59 99 (accept_3_4 28 59 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 59 99 (Polychromatic418967fa.accept_13_1_7_8_1_1796 27 59 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 59 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 26
  59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 99 (accept_3_4 25 59 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 99 (Polychromatic418967fa.accept_16_8_11_3_1_4279
  24 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 99
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 99 (accept_3_4 22 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 59
  99 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 59 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 59 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 99 (accept_3_4 19 59 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 59 99 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 59 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 99 (Polychromatic418967fa.accept_19_17_2_4_1_4278
  17 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 59 99 (accept_3_4 16 59
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 59 99
  (Polychromatic418967fa.accept_13_2_7_8_1_4221 15 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 59 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 59 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 99 (accept_3_4 13 59 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 59 99 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 59 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 99 (Polychromatic418967fa.accept_7_4_3_1_1_87 11
  59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 59 99 (accept_3_4 10 59 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 59 99 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 59
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 59 99
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 59 99 (accept_3_4 7 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 99
  (Polychromatic418967fa.accept_15_6_14_9_1_1471 6 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 59 99 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 59 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 99 (accept_3_4 4 59 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 59 99 (Polychromatic418967fa.accept_13_3_7_8_1_4192 3 59 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 59
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 99 (accept_3_4 1 59 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59 99))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 58 99
  (Eq.refl Bool.true) (allA_succ_of_accept 41 58 99 (accept_3_5 41 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 58 99 (Polychromatic418967fa.accept_13_1_6_8_1_208 40 58 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 58 99 (Polychromatic418967fa.accept_16_7_10_3_1_2210 39 58 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 58 99 (accept_3_5 38 58 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 58 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 58
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 58 99
  (Polychromatic418967fa.accept_14_8_2_1_1_1652 36 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 58 99 (accept_3_5 35 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 58
  99 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 58 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 58 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 58 99 (accept_3_5 32 58 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 58 99 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 58 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 58 99 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  30 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 58 99 (accept_3_5 29 58
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 58 99
  (Polychromatic418967fa.accept_13_2_6_8_1_1092 28 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 58 99 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 58 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 58 99 (accept_3_5 26 58 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 58 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 58 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 58 99 (Polychromatic418967fa.accept_7_3_2_1_1_225 24
  58 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 58 99 (accept_3_5 23 58 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 58 99 (Polychromatic418967fa.accept_14_8_2_1_1_1652
  22 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 58 99
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 58 99 (accept_3_5 20 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 58
  99 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 58 99 (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 58 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 58 99 (accept_3_5 17 58 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 58 99 (Polychromatic418967fa.accept_19_16_1_4_1_4235 16 58 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 58 99 (Polychromatic418967fa.accept_13_2_6_8_1_1092
  15 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 58 99 (accept_3_5 14 58
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 58 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 13
  58 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 58 99
  (Polychromatic418967fa.accept_16_12_10_3_1_4209 12 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 58 99 (accept_3_5 11 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 58
  99 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 58 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 8 58 99 (accept_3_5 8 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 58 99 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 58 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 58 99 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 58 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 58 99 (accept_3_5 5 58 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 58 99 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 58 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 58 99
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 58 99 (accept_3_5 2 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 58 99
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 58 99)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 57 99 (Eq.refl Bool.true) (allA_succ_of_gcd
  42 57 99 3 14 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 57 99 (Polychromatic418967fa.accept_12_5_9_3_1_85 41 57 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 99 (Polychromatic418967fa.accept_13_1_5_8_1_207 40 57 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 57 99 3 13 19 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 57 99
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 57 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 99 (Polychromatic418967fa.accept_12_1_9_3_1_370 37 57 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 57 99 3 12 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 57 99 (Polychromatic418967fa.accept_12_11_9_3_1_792 35 57 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 99
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 57 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 57 99 3 11 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 57 99 (Polychromatic418967fa.accept_10_2_7_9_1_783 32 57 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 99 (Polychromatic418967fa.accept_12_7_9_3_1_767 31 57 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 57 99 3 10 19 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 57 99
  (Polychromatic418967fa.accept_12_5_9_3_1_85 29 57 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 57 99 (Polychromatic418967fa.accept_10_8_7_9_1_425 28 57 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 57 99 3 9 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 57 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 57 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 99
  (Polychromatic418967fa.accept_12_1_9_3_1_370 25 57 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 57 99 3 8 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 57 99 (Polychromatic418967fa.accept_12_11_9_3_1_792 23 57 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 57 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 57 99 3 7 19 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 57 99
  (Polychromatic418967fa.accept_15_5_12_9_1_2253 20 57 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 99 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 57 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 57 99 3 6 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 57 99 (Polychromatic418967fa.accept_12_5_9_3_1_85 17 57 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 99
  (Polychromatic418967fa.accept_13_3_5_8_1_1099 16 57 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 57 99 3 5 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 57 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 57 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 99 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 57 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 57 99 3 4 19 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 57 99
  (Polychromatic418967fa.accept_12_11_9_3_1_792 11 57 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 57 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 57 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 57 99 3 3 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 57 99 (Polychromatic418967fa.accept_10_8_7_9_1_425 8 57 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 99
  (Polychromatic418967fa.accept_12_7_9_3_1_767 7 57 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 57 99 3 2 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 57 99 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 57 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 99 (Polychromatic418967fa.accept_15_4_12_9_1_773 4 57 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 57 99 3 1 19 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 57 99
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 57 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 57 99 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 57 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 57 99))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 56 99
  (Eq.refl Bool.true) (allA_succ_of_accept 43 56 99 (accept_3_4 43 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 56 99 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 56 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 56 99 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 56 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 99 (accept_3_4 40 56 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 99 (Polychromatic418967fa.accept_18_3_2_9_1_1013
  39 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 99
  (Polychromatic418967fa.accept_13_12_4_8_1_1120 38 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 56 99 (accept_3_4 37 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 56
  99 (Polychromatic418967fa.accept_13_10_4_8_1_2570 36 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 56 99 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 56 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 99 (accept_3_4 34 56 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 99 (Polychromatic418967fa.accept_10_3_6_9_1_779 33 56 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 99
  (Polychromatic418967fa.accept_15_2_11_9_1_263 32 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 56 99 (accept_3_4 31 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 56
  99 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 56 99 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 56 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 99 (accept_3_4 28 56 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 56 99 (Polychromatic418967fa.accept_16_11_8_3_1_3183 27 56 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 99 (Polychromatic418967fa.accept_17_9_5_14_1_4277
  26 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 56 99 (accept_3_4 25 56
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 56 99
  (Polychromatic418967fa.accept_13_11_4_8_1_1098 24 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 56 99 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 56 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 99 (accept_3_4 22 56 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 56 99 (Polychromatic418967fa.accept_15_6_11_9_1_3215 21 56 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 99 (Polychromatic418967fa.accept_15_5_11_9_1_4276
  20 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 56 99 (accept_3_4 19 56
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 56 99 (Polychromatic418967fa.accept_12_6_8_3_1_82
  18 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 56 99
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 56 99 (accept_3_4 16 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 56
  99 (Polychromatic418967fa.accept_10_5_6_9_1_2235 15 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 56 99 (Polychromatic418967fa.accept_19_14_18_4_1_4275 14 56 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 56 99 (accept_3_4 13 56 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 56 99 (Polychromatic418967fa.accept_13_12_4_8_1_1120 12 56 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 56 99 (Polychromatic418967fa.accept_6_5_2_3_1_81 11
  56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 99 (accept_3_4 10 56 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 99 (Polychromatic418967fa.accept_13_9_4_8_1_1752 9
  56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 99
  (Polychromatic418967fa.accept_19_8_18_4_1_4274 8 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 56 99 (accept_3_4 7 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56 99
  (Polychromatic418967fa.accept_12_6_8_3_1_82 6 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 56 99 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 56 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 99 (accept_3_4 4 56 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 56 99 (Polychromatic418967fa.accept_10_3_6_9_1_779 3 56 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 99 (Polychromatic418967fa.accept_15_2_11_9_1_263 2
  56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 99 (accept_3_4 1 56 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 99)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 55
  99 (Eq.refl Bool.true) (allA_succ_of_gcd 44 55 99 11 4 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 55 99 (Polychromatic418967fa.accept_16_11_7_3_1_3163 43 55 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 99
  (Polychromatic418967fa.accept_15_12_10_9_1_798 42 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 99 (accept_3_5 41 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 55
  99 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 55 99 (Polychromatic418967fa.accept_18_3_1_9_1_1929 39 55 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 99 (accept_3_5 38 55 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 55 99 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 55 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 99 (Polychromatic418967fa.accept_8_4_7_3_1_144 36
  55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 55 99 (accept_3_5 35 55 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 55 99 (Polychromatic418967fa.accept_6_4_1_3_1_77 34
  55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 55 99 11 3 5 9 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 55 99 (accept_3_5 32 55
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 99 (Polychromatic418967fa.accept_10_1_5_9_1_157
  31 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 99
  (Polychromatic418967fa.accept_7_2_6_1_1_73 30 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 55 99 (accept_3_5 29 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 55
  99 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 55 99 (Polychromatic418967fa.accept_15_12_10_9_1_798 27 55 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 99 (accept_3_5 26 55 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 55 99 (Polychromatic418967fa.accept_16_9_7_3_1_614 25 55 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 99 (Polychromatic418967fa.accept_10_4_5_9_1_1231
  24 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 99 (accept_3_5 23 55
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 55 99 11 2 5 9 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 55 99
  (Polychromatic418967fa.accept_10_1_5_9_1_157 21 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 55 99 (accept_3_5 20 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 55
  99 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 55 99 (Polychromatic418967fa.accept_13_5_3_8_1_1117 18 55 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 99 (accept_3_5 17 55 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 55 99 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 55 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 55 99 (Polychromatic418967fa.accept_16_15_7_3_1_4273
  15 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 99 (accept_3_5 14 55
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 99
  (Polychromatic418967fa.accept_17_13_4_14_1_4272 13 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 55 99 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 55 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 55 99 11 1 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 55 99 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 55 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 99
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 55 99 (accept_3_5 8 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 99
  (Polychromatic418967fa.accept_13_7_3_8_1_1750 7 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 55 99 (Polychromatic418967fa.accept_10_6_5_9_1_1233 6 55 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 55 99 (accept_3_5 5 55 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 55 99 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 55 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 99 (Polychromatic418967fa.accept_15_3_10_9_1_769 3
  55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 99 (accept_3_5 2 55 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 99 (Polychromatic418967fa.accept_10_1_5_9_1_157 1
  55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55
  99))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 54 99 (Eq.refl Bool.true) (allA_succ_of_gcd 45 54 99 9
  5 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 54 99
  (Polychromatic418967fa.accept_12_8_6_3_1_366 44 54 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 54 99 (Polychromatic418967fa.accept_10_3_4_9_1_15 43 54 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 99 3 14 18 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 54 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 99
  (Polychromatic418967fa.accept_12_4_6_3_1_332 40 54 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 54 99 3 13 18 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 54 99 (Polychromatic418967fa.accept_7_3_5_1_1_72 38 54 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 54 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 99 9 4 6 11 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 99
  (Polychromatic418967fa.accept_10_5_4_9_1_420 35 54 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 54 99 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 54 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 54 99 3 11 18 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 54 99 (Polychromatic418967fa.accept_7_4_5_1_1_418 32 54 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 99
  (Polychromatic418967fa.accept_7_3_5_1_1_72 31 54 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 54 99 3 10 18 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 54 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 54 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 99 (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 54 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 54 99 9 3 6 11 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 54 99
  (Polychromatic418967fa.accept_12_2_6_3_1_331 26 54 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 54 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 54 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 99 3 8 18 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 99 (Polychromatic418967fa.accept_10_3_4_9_1_15 23 54 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 99
  (Polychromatic418967fa.accept_12_10_6_3_1_786 22 54 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 54 99 3 7 18 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 54 99 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 54 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 99 (Polychromatic418967fa.accept_13_6_2_8_1_1782 19 54 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 99 9 2 6 11 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 99
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 54 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 54 99 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 54 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 54 99 3 5 18 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 54 99 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 54 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 99
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 54 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 54 99 3 4 18 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 54 99 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 54 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 99 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 54 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 54 99 9 1 6 11 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 54 99
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 54 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 54 99 (Polychromatic418967fa.accept_13_7_2_8_1_1746 7 54 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 99 3 2 18 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 54 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 99
  (Polychromatic418967fa.accept_7_4_5_1_1_418 4 54 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 54 99 3 1 18 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 54 99 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 54 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 54 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  99)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 53 99 (Eq.refl Bool.true) (allA_succ_of_accept 46 53
  99 (accept_3_4 46 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 99
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 53 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 53 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 99 (accept_3_4 43 53 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 53 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 53 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 99 (Polychromatic418967fa.accept_22_19_9_11_1_4271
  41 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 99 (accept_3_4 40 53
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 99
  (Polychromatic418967fa.accept_17_5_2_14_1_4270 39 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 53 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 53 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 99 (accept_3_4 37 53 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 53 99 (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 53 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 99 (Polychromatic418967fa.accept_13_9_1_8_1_1742
  35 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 53 99 (accept_3_4 34 53
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 53 99 (Polychromatic418967fa.accept_7_5_4_1_1_412
  33 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 53 99
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 53 99 (accept_3_4 31 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 53
  99 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 53 99 (Polychromatic418967fa.accept_15_14_8_9_1_1452 29 53 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 99 (accept_3_4 28 53 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 53 99 (Polychromatic418967fa.accept_19_8_15_4_1_2953 27 53 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 53 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 26
  53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 99 (accept_3_4 25 53 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 99 (Polychromatic418967fa.accept_7_3_4_1_1_71 24
  53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 99
  (Polychromatic418967fa.accept_29_23_24_12_1_4269 23 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 99 (accept_3_4 22 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 53
  99 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 53 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 53 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 99 (accept_3_4 19 53 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 53 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 53 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 99 (Polychromatic418967fa.accept_7_3_4_1_1_71 17
  53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 99 (accept_3_4 16 53 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 53 99 (Polychromatic418967fa.accept_18_15_17_9_1_4200
  15 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 99
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 53 99 (accept_3_4 13 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 53
  99 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 53 99 (Polychromatic418967fa.accept_13_11_1_8_1_1776 11 53 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 99 (accept_3_4 10 53 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 53 99 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 53 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 53
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 99 (accept_3_4 7 53 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 53
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 99
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 99 (accept_3_4 4 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53 99
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 53 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 99 (accept_3_4 1 53 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 99))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 52 99 (Eq.refl Bool.true)
  (allA_succ_of_accept 47 52 99 (accept_3_5 47 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 52
  99 (Polychromatic418967fa.accept_7_4_3_1_1_87 46 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 52 99 (Polychromatic418967fa.accept_19_7_14_4_1_4268 45 52 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 99 (accept_3_5 44 52 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 52 99 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 52 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 99 (Polychromatic418967fa.accept_12_6_4_3_1_361 42
  52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 52 99 (accept_3_5 41 52 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 52 99 (Polychromatic418967fa.accept_7_5_3_1_1_424 40
  52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 52 99
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 52 99 (accept_3_5 38 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 52
  99 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 52 99 (Polychromatic418967fa.accept_22_14_8_11_1_2777 36 52 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 52 99 (accept_3_5 35 52 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 52 99 (Polychromatic418967fa.accept_19_15_14_4_1_4267 34 52 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 52 99 (Polychromatic418967fa.accept_7_5_3_1_1_424 33
  52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 52 99 (accept_3_5 32 52 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 52 99 (Polychromatic418967fa.accept_6_1_4_3_1_14 31
  52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 52 99
  (Polychromatic418967fa.accept_7_2_3_1_1_10 30 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 52 99 (accept_3_5 29 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 52
  99 (Polychromatic418967fa.accept_15_13_7_9_1_3210 28 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 52 99 (Polychromatic418967fa.accept_10_7_2_9_1_775 27 52 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 52 99 (accept_3_5 26 52 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 52 99 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 52 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 99
  (Polychromatic418967fa.accept_16_8_4_3_1_3146 24 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 52 99 (accept_3_5 23 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 52
  99 (Polychromatic418967fa.accept_16_6_4_3_1_2189 22 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 52 99 (Polychromatic418967fa.accept_10_1_2_9_1_152 21 52 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 52 99 (accept_3_5 20 52 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 52 99 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 52 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 52 99 (Polychromatic418967fa.accept_7_4_3_1_1_87 18
  52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 52 99 (accept_3_5 17 52 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 52 99 (Polychromatic418967fa.accept_7_2_3_1_1_10 16
  52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 52 99
  (Polychromatic418967fa.accept_8_7_4_3_1_156 15 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 52 99 (accept_3_5 14 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 52
  99 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 52 99 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 52 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 52 99 (accept_3_5 11 52 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 52 99 (Polychromatic418967fa.accept_17_10_1_14_1_489 10 52 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 52 99 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 52
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 99 (accept_3_5 8 52 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 52 99 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 52
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 99
  (Polychromatic418967fa.accept_12_6_4_3_1_361 6 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 52 99 (accept_3_5 5 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52 99
  (Polychromatic418967fa.accept_7_4_3_1_1_87 4 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 52 99 (Polychromatic418967fa.accept_21_3_10_15_1_4266 3 52 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 99 (accept_3_5 2 52 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 52 99 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 52 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52 99)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  49 51 99 (Eq.refl Bool.true) (allA_succ_of_gcd 48 51 99 3 16 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 51 99 (Polychromatic418967fa.accept_18_11_15_9_1_360 47 51 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 99
  (Polychromatic418967fa.accept_13_7_12_8_1_199 46 51 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 51 99 3 15 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 51 99 (Polychromatic418967fa.accept_13_5_12_8_1_198 44 51 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 99 (Polychromatic418967fa.accept_13_4_12_8_1_197 43 51 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 51 99 3 14 17 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 51 99
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 51 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 51 99 (Polychromatic418967fa.accept_13_1_12_8_1_1818 40 51 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 51 99 3 13 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 51 99 (Polychromatic418967fa.accept_7_3_2_1_1_225 38 51 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 99
  (Polychromatic418967fa.accept_21_16_9_15_1_4265 37 51 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 51 99 3 12 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 51 99 (Polychromatic418967fa.accept_10_5_1_9_1_791 35 51 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 99 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 51 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 51 99 3 11 17 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 51 99
  (Polychromatic418967fa.accept_10_2_1_9_1_1248 32 51 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 99 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 51 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 51 99 3 10 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 51 99 (Polychromatic418967fa.accept_15_14_6_9_1_2274 29 51 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 99
  (Polychromatic418967fa.accept_10_8_1_9_1_413 28 51 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 51 99 3 9 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 51 99 (Polychromatic418967fa.accept_15_11_6_9_1_3236 26 51 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 99 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 51 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 51 99 3 8 17 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 51 99
  (Polychromatic418967fa.accept_13_10_12_8_1_2550 23 51 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 51 99 (Polychromatic418967fa.accept_10_2_1_9_1_1248 22 51 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 51 99 3 7 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 51 99 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 51 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 99
  (Polychromatic418967fa.accept_15_4_6_9_1_2269 19 51 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 51 99 3 6 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 51 99 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 51 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 99 (Polychromatic418967fa.accept_15_1_6_9_1_254 16 51 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 51 99 3 5 17 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 51 99
  (Polychromatic418967fa.accept_13_1_12_8_1_1818 14 51 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 99 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 51 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 51 99 3 4 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 51 99 (Polychromatic418967fa.accept_15_11_6_9_1_3236 11 51 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 99
  (Polychromatic418967fa.accept_7_3_2_1_1_225 10 51 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 51 99 3 3 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 51 99 (Polychromatic418967fa.accept_10_8_1_9_1_413 8 51 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 99 (Polychromatic418967fa.accept_13_7_12_8_1_199 7 51 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 51 99 3 2 17 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 51 99
  (Polychromatic418967fa.accept_10_5_1_9_1_791 5 51 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 51 99 (Polychromatic418967fa.accept_13_4_12_8_1_197 4 51 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 51 99 3 1 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 51 99 (Polychromatic418967fa.accept_10_2_1_9_1_1248 2 51 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 99
  (Polychromatic418967fa.accept_13_1_12_8_1_1818 1 51 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 51 99))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 99 (allA_succ_of_accept 49 50 99
  (accept_3_4 49 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 50 99
  (Polychromatic418967fa.accept_13_9_11_8_1_195 48 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 50 99 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 50 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 99 (accept_3_4 46 50 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 50 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 50 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 99 (Polychromatic418967fa.accept_14_2_8_1_1_1647
  44 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 50 99 (accept_3_4 43 50
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 50 99 (Polychromatic418967fa.accept_12_6_2_3_1_354
  42 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 50 99
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 50 99 (accept_3_4 40 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 50
  99 (Polychromatic418967fa.accept_18_3_14_9_1_4264 39 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 50 99 (Polychromatic418967fa.accept_16_6_2_3_1_4223 38 50 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 50 99 (accept_3_4 37 50 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 50 99 (Polychromatic418967fa.accept_13_10_11_8_1_1770 36 50 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 50 99
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 50 99 (accept_3_4 34 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 50
  99 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 50 99 (Polychromatic418967fa.accept_13_6_11_8_1_1111 32 50 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 50 99 (accept_3_4 31 50 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 50 99 (Polychromatic418967fa.accept_12_6_2_3_1_354 30 50 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 50 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 50
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 99 (accept_3_4 28 50 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 99 (Polychromatic418967fa.accept_13_1_11_8_1_2562
  27 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 99
  (Polychromatic418967fa.accept_15_11_5_9_1_3205 26 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 50 99 (accept_3_4 25 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 50
  99 (Polychromatic418967fa.accept_18_6_14_9_1_3039 24 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 50 99 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 50 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 99 (accept_3_4 22 50 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 50 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 99
  (Polychromatic418967fa.accept_19_1_12_4_1_4263 20 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 50 99 (accept_3_4 19 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 50
  99 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 50 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 50 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 99 (accept_3_4 16 50 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 50 99 (Polychromatic418967fa.accept_16_15_2_3_1_4262 15 50 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 99 (Polychromatic418967fa.accept_13_1_11_8_1_2562
  14 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 50 99 (accept_3_4 13 50
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 50 99
  (Polychromatic418967fa.accept_15_12_5_9_1_3234 12 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 50 99 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 50 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 99 (accept_3_4 10 50 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 50 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 50 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 99 (Polychromatic418967fa.accept_17_8_16_14_1_4261
  8 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 50 99 (accept_3_4 7 50 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50 99 (Polychromatic418967fa.accept_12_6_2_3_1_354 6
  50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 50 99
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 50 99 (accept_3_4 4 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 50 99
  (Polychromatic418967fa.accept_13_3_11_8_1_1094 3 50 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 50 99 (Polychromatic418967fa.accept_14_2_8_1_1_1647 2 50 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 99 (accept_3_4 1 50 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 50 99)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 99 (allA_succ_of_accept 48
  49 99 (Polychromatic418967fa.accept_14_6_7_1_1_78 48 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 49 99 (accept_3_5 47 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 49 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 49 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 99 (Polychromatic418967fa.accept_12_9_1_3_1_350 45 49 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 99 (accept_3_5 44 49 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 99 (Polychromatic418967fa.accept_13_4_10_8_1_1817
  43 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 49 99
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 49 99 (accept_3_5 41 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 49
  99 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 49 99 (Polychromatic418967fa.accept_18_3_13_9_1_4260 39 49 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 99 (accept_3_5 38 49 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 49 99 (Polychromatic418967fa.accept_13_11_10_8_1_1804 37 49 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 99 (Polychromatic418967fa.accept_14_8_7_1_1_1615
  36 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 99 (accept_3_5 35 49
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 99 (Polychromatic418967fa.accept_4_2_1_3_1_27
  34 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 99
  (Polychromatic418967fa.accept_12_9_1_3_1_350 33 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 99 (accept_3_5 32 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 49
  99 (Polychromatic418967fa.accept_13_5_10_8_1_1127 31 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 49 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 99 (accept_3_5 29 49 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 99 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 49 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 99
  (Polychromatic418967fa.accept_14_13_7_1_1_1618 27 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 99 (accept_3_5 26 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 49
  99 (Polychromatic418967fa.accept_13_12_10_8_1_3343 25 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 99 (Polychromatic418967fa.accept_13_11_10_8_1_1804 24 49 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 99 (accept_3_5 23 49 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 49 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 99
  (Polychromatic418967fa.accept_12_9_1_3_1_350 21 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 99 (accept_3_5 20 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 49
  99 (Polychromatic418967fa.accept_21_19_7_15_1_2848 19 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 49 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 49 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 99 (accept_3_5 17 49 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 99 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 49 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 99
  (Polychromatic418967fa.accept_13_2_10_8_1_1126 15 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 99 (accept_3_5 14 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 49
  99 (Polychromatic418967fa.accept_14_13_7_1_1_1618 13 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 99 (Polychromatic418967fa.accept_13_12_10_8_1_3343 12 49 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 99 (accept_3_5 11 49 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 49 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 99
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 99 (accept_3_5 8 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 99
  (Polychromatic418967fa.accept_13_7_10_8_1_567 7 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 49 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 49 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 99 (accept_3_5 5 49 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 49 99 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 49 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 99 (Polychromatic418967fa.accept_17_3_15_14_1_4219
  3 49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 99 (accept_3_5 2 49 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 99 (Polychromatic418967fa.accept_21_1_7_15_1_4259 1
  49 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49
  99))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 99 (allA_succ_of_accept 47 48 99
  (Polychromatic418967fa.accept_7_5_6_1_1_407 47 48 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 48 99 (Polychromatic418967fa.accept_13_7_9_8_1_188 46 48 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 48 99 3 15 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 48 99 (Polychromatic418967fa.accept_7_2_6_1_1_73 44 48 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 99
  (Polychromatic418967fa.accept_13_4_9_8_1_1736 43 48 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 48 99 3 14 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 48 99 (Polychromatic418967fa.accept_10_1_8_9_1_787 41 48 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 99 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 48 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 48 99 3 13 16 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 48 99
  (Polychromatic418967fa.accept_13_12_9_8_1_2595 38 48 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 48 99 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 48 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 99 3 12 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 99 (Polychromatic418967fa.accept_14_7_6_1_1_1656 35 48 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 48 99
  (Polychromatic418967fa.accept_10_4_8_9_1_784 34 48 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 48 99 3 11 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 48 99 (Polychromatic418967fa.accept_19_13_10_4_1_4258 32 48 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 99 (Polychromatic418967fa.accept_10_1_8_9_1_787 31 48 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 99 3 10 16 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 99
  (Polychromatic418967fa.accept_13_3_9_8_1_4202 29 48 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 48 99 (Polychromatic418967fa.accept_15_13_3_9_1_1482 28 48 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 48 99 3 9 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 48 99 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 48 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 99
  (Polychromatic418967fa.accept_13_12_9_8_1_2595 25 48 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 48 99 3 8 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 48 99 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 48 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 48 99 (Polychromatic418967fa.accept_18_4_12_9_1_2011 22 48 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 48 99 3 7 16 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 48 99
  (Polychromatic418967fa.accept_13_7_9_8_1_188 20 48 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 48 99 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 48 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 99 3 6 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 99 (Polychromatic418967fa.accept_10_7_8_9_1_785 17 48 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 48 99
  (Polychromatic418967fa.accept_7_2_6_1_1_73 16 48 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 48 99 3 5 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 48 99 (Polychromatic418967fa.accept_10_4_8_9_1_784 14 48 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 99 (Polychromatic418967fa.accept_15_13_3_9_1_1482 13 48 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 99 3 4 16 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 99
  (Polychromatic418967fa.accept_10_1_8_9_1_787 11 48 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 48 99 (Polychromatic418967fa.accept_15_10_3_9_1_3285 10 48 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 48 99 3 3 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 48 99 (Polychromatic418967fa.accept_15_8_3_9_1_4220 8 48 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 99
  (Polychromatic418967fa.accept_10_7_8_9_1_785 7 48 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 48 99 3 2 16 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 48 99 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 48 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48 99 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 48 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 48 99 3 1 16 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 48 99
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 48 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 48 99 (Polychromatic418967fa.accept_10_1_8_9_1_787 1 48 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 48 99)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 99
  (allA_succ_of_accept 46 47 99 (accept_3_4 46 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47
  99 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 47 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 99 (accept_3_4 43 47 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 99 (Polychromatic418967fa.accept_10_2_7_9_1_783 42 47 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 99 (Polychromatic418967fa.accept_7_6_5_1_1_416 41
  47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 99 (accept_3_4 40 47 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 99 (Polychromatic418967fa.accept_7_4_5_1_1_418 39
  47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 47 99
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 47 99 (accept_3_4 37 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 47
  99 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 47 99 (Polychromatic418967fa.accept_17_1_13_14_1_478 35 47 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 99 (accept_3_4 34 47 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 47 99 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 47 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 47 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 32
  47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 99 (accept_3_4 31 47 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 99 (Polychromatic418967fa.accept_18_12_11_9_1_4257
  30 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 99
  (Polychromatic418967fa.accept_16_13_15_3_1_4196 29 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 99 (accept_3_4 28 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 47
  99 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 47 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 47 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 99 (accept_3_4 25 47 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 47 99 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 47 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 99 (Polychromatic418967fa.accept_15_8_2_9_1_3200
  23 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 99 (accept_3_4 22 47
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 99
  (Polychromatic418967fa.accept_12_9_11_3_1_772 21 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 47 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 47 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 99 (accept_3_4 19 47 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 47 99 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 47 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 99 (Polychromatic418967fa.accept_7_3_5_1_1_72 17
  47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 99 (accept_3_4 16 47 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 99 (Polychromatic418967fa.accept_18_15_11_9_1_4256
  15 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 99
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 47 99 (accept_3_4 13 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 47
  99 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 47 99 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 47 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 99 (accept_3_4 10 47 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 47 99 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 47 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 47
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 99 (accept_3_4 7 47 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 99 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 47
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 99
  (Polychromatic418967fa.accept_19_5_9_4_1_232 5 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 99 (accept_3_4 4 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47 99
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 47 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 47 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 99 (accept_3_4 1 47 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 99))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 99 (allA_succ_of_accept 45 46
  99 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 46 99 (accept_3_5 44 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 46
  99 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 46 99 (Polychromatic418967fa.accept_12_6_10_3_1_1313 42 46 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 99 (accept_3_5 41 46 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 46 99 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 46 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 46 99 (Polychromatic418967fa.accept_14_11_4_1_1_4255
  39 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 46 99 (accept_3_5 38 46
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 46 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 37
  46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 46 99
  (Polychromatic418967fa.accept_13_10_7_8_1_1794 36 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 46 99 (accept_3_5 35 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 46
  99 (Polychromatic418967fa.accept_19_15_8_4_1_2962 34 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 46 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 46 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 46 99 (accept_3_5 32 46 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 46 99 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 46 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 46 99
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 30 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 46 99 (accept_3_5 29 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 46
  99 (Polychromatic418967fa.accept_13_2_7_8_1_4221 28 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 46 99 (Polychromatic418967fa.accept_13_1_7_8_1_1796 27 46 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 46 99 (accept_3_5 26 46 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 46 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 46 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 46 99 (Polychromatic418967fa.accept_7_3_4_1_1_71 24
  46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 99 (accept_3_5 23 46 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 99 (Polychromatic418967fa.accept_13_9_7_8_1_1122
  22 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 99
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 46 99 (accept_3_5 20 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 46
  99 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 46 99 (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 46 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 99 (accept_3_5 17 46 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 46 99 (Polychromatic418967fa.accept_13_3_7_8_1_4192 16 46 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 99 (Polychromatic418967fa.accept_10_5_6_9_1_2235
  15 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 46 99 (accept_3_5 14 46
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 46 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 13
  46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 46 99
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 46 99 (accept_3_5 11 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 46
  99 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 46 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 8 46 99 (accept_3_5 8 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 46 99 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 46 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 46 99 (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 46 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 99 (accept_3_5 5 46 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 46 99 (Polychromatic418967fa.accept_25_4_21_24_1_4254 4 46 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 99
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 46 99 (accept_3_5 2 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 99
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 46 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 46 99)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 99 (allA_succ_of_accept 44 45 99
  (Polychromatic418967fa.accept_7_2_3_1_1_10 44 45 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 99 (Polychromatic418967fa.accept_12_7_9_3_1_767 43 45 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 45 99 3 14 15 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 45 99 (Polychromatic418967fa.accept_10_1_5_9_1_157 41 45 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 99
  (Polychromatic418967fa.accept_7_5_3_1_1_424 40 45 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 45 99 3 13 15 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 45 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 45 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 99 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 45 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 45 99 9 4 5 11 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 45 99
  (Polychromatic418967fa.accept_12_11_9_3_1_792 35 45 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 45 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 45 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 45 99 3 11 15 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 45 99 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 45 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 99
  (Polychromatic418967fa.accept_10_1_5_9_1_157 31 45 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 45 99 3 10 15 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 45 99 (Polychromatic418967fa.accept_12_5_9_3_1_85 29 45 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 99 (Polychromatic418967fa.accept_13_2_6_8_1_1092 28 45 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 45 99 9 3 5 11 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 45 99
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 45 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 99 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 45 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 45 99 3 8 15 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 99 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 45 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 99
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 45 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 45 99 3 7 15 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 45 99 (Polychromatic418967fa.accept_17_3_11_14_1_2071 20 45 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 99 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 45 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 45 99 9 2 5 11 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 45 99
  (Polychromatic418967fa.accept_12_5_9_3_1_85 17 45 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 45 99 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 45 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 99 3 5 15 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 45 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 99
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 45 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 45 99 3 4 15 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 45 99 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 45 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 45 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 45 99 9 1 5 11 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 45 99
  (Polychromatic418967fa.accept_16_8_13_3_1_4253 8 45 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 99 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 45 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 99 3 2 15 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 45 99 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 45 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 99
  (Polychromatic418967fa.accept_7_4_3_1_1_87 4 45 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 45 99 3 1 15 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 45 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 45 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 99 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 45 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  99))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 99 (allA_succ_of_accept 43 44 99 (accept_3_4 43 44 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 44 99 (Polychromatic418967fa.accept_12_6_8_3_1_82 42
  44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 44 99
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 44 99 (accept_3_4 40 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 44
  99 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 44 99 (Polychromatic418967fa.accept_7_3_2_1_1_225 38 44 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 44 99 (accept_3_4 37 44 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 44 99 (Polychromatic418967fa.accept_13_10_5_8_1_2555 36 44 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 44 99 (Polychromatic418967fa.accept_6_5_2_3_1_81 35
  44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 99 (accept_3_4 34 44 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 44 99 11 3 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 44 99 (Polychromatic418967fa.accept_19_13_6_4_1_4207
  32 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 44 99 (accept_3_4 31 44
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 44 99 (Polychromatic418967fa.accept_12_6_8_3_1_82
  30 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 44 99
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 44 99 (accept_3_4 28 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 44
  99 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 44 99 (Polychromatic418967fa.accept_16_10_12_3_1_4252 26 44 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 44 99 (accept_3_4 25 44 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 44 99 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 44 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 44 99 (Polychromatic418967fa.accept_6_5_2_3_1_81 23
  44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 44 99 11 2 4 9 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 44 99
  (Polychromatic418967fa.accept_15_6_14_9_1_1471 21 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 44 99 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 44 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 44 99 (accept_3_4 19 44 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 44 99 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 44 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 44 99 (Polychromatic418967fa.accept_6_5_2_3_1_81 17
  44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 99 (accept_3_4 16 44 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 44 99 (Polychromatic418967fa.accept_8_7_4_3_1_156 15
  44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 99
  (Polychromatic418967fa.accept_13_1_5_8_1_207 14 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 44 99 (accept_3_4 13 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 44
  99 (Polychromatic418967fa.accept_13_12_5_8_1_1101 12 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 11 44 99 11 1 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 10 44 99 (accept_3_4 10 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 44 99 (Polychromatic418967fa.accept_16_9_12_3_1_3138 9 44 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 99 (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 44 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 44 99 (accept_3_4 7 44 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44 99 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 44 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 44 99
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 44 99 (accept_3_4 4 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 44 99
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 44 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 44 99 (Polychromatic418967fa.accept_19_2_6_4_1_4251 2 44 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 99 (accept_3_4 1 44 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 44 99)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 99 (allA_succ_of_accept 42 43 99
  (Polychromatic418967fa.accept_18_6_7_9_1_4250 42 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 99 (accept_3_5 41 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 43
  99 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 43 99 (Polychromatic418967fa.accept_16_7_11_3_1_1330 39 43 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 99 (accept_3_5 38 43 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 43 99 (Polychromatic418967fa.accept_13_11_4_8_1_1098 37 43 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 99 (Polychromatic418967fa.accept_10_6_3_9_1_1207
  36 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 43 99 (accept_3_5 35 43
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 43 99 (Polychromatic418967fa.accept_6_4_1_3_1_77
  34 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 43 99
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 43 99 (accept_3_5 32 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 43
  99 (Polychromatic418967fa.accept_16_15_11_3_1_2179 31 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 43 99 (Polychromatic418967fa.accept_16_14_11_3_1_4249 30 43 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 99 (accept_3_5 29 43 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 43 99 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 43 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 99
  (Polychromatic418967fa.accept_19_8_5_4_1_4248 27 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 43 99 (accept_3_5 26 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 43
  99 (Polychromatic418967fa.accept_13_12_4_8_1_1120 25 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 43 99 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 43 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 43 99 (accept_3_5 23 43 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 43 99 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 43 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 99
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 43 99 (accept_3_5 20 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 43
  99 (Polychromatic418967fa.accept_15_4_13_9_1_3197 19 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 43 99 (Polychromatic418967fa.accept_15_3_13_9_1_3196 18 43 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 43 99 (accept_3_5 17 43 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 43 99 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 43 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 43 99
  (Polychromatic418967fa.accept_16_15_11_3_1_2179 15 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 43 99 (accept_3_5 14 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 43
  99 (Polychromatic418967fa.accept_23_13_20_7_1_4247 13 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 43 99 (Polychromatic418967fa.accept_13_12_4_8_1_1120 12 43 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 99 (accept_3_5 11 43 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 43 99 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 43 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 99
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 43 99 (accept_3_5 8 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 99
  (Polychromatic418967fa.accept_15_7_13_9_1_1466 7 43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 43 99 (Polychromatic418967fa.accept_10_6_3_9_1_1207 6 43 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 43 99 (accept_3_5 5 43 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 43 99 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 43 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 43 99 (Polychromatic418967fa.accept_15_3_13_9_1_3196 3
  43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 99 (accept_3_5 2 43 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 99 (Polychromatic418967fa.accept_19_1_5_4_1_4246 1
  43 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43
  99))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 99 (allA_succ_of_accept 41 42 99
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 42 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 99 (Polychromatic418967fa.accept_12_4_6_3_1_332 40 42 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 42 99 3 13 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 42 99 (Polychromatic418967fa.accept_12_2_6_3_1_331 38 42 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 99
  (Polychromatic418967fa.accept_4_1_2_3_1_9 37 42 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 42 99 3 12 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 42 99 (Polychromatic418967fa.accept_13_9_3_8_1_573 35 42 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 42 99 (Polychromatic418967fa.accept_12_10_6_3_1_786 34 42 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 42 99 3 11 14 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 42 99
  (Polychromatic418967fa.accept_12_8_6_3_1_366 32 42 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 42 99 (Polychromatic418967fa.accept_10_1_2_9_1_152 31 42 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 99 3 10 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 42 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 42 99
  (Polychromatic418967fa.accept_12_4_6_3_1_332 28 42 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 42 99 3 9 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 42 99 (Polychromatic418967fa.accept_12_2_6_3_1_331 26 42 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 42 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 99 3 8 14 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 99
  (Polychromatic418967fa.accept_16_7_10_3_1_2210 23 42 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 42 99 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 42 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 42 99 3 7 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 42 99 (Polychromatic418967fa.accept_12_8_6_3_1_366 20 42 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 99
  (Polychromatic418967fa.accept_15_4_12_9_1_773 19 42 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 42 99 3 6 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 42 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 42 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 42 99 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 42 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 42 99 3 5 14 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 42 99
  (Polychromatic418967fa.accept_12_2_6_3_1_331 14 42 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 42 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 42 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 99 3 4 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 99 (Polychromatic418967fa.accept_10_1_2_9_1_152 11 42 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 42 99
  (Polychromatic418967fa.accept_12_10_6_3_1_786 10 42 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 42 99 3 3 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 42 99 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 42 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 99 (Polychromatic418967fa.accept_10_7_2_9_1_775 7 42 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 99 3 2 14 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 99
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 42 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 42 99 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 42 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 42 99 3 1 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 42 99 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 42 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 99
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 42 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 42 99)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 99 (allA_succ_of_accept 40 41 99 (accept_3_4
  40 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 99
  (Polychromatic418967fa.accept_16_7_9_3_1_1324 39 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 41 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 99 (accept_3_4 37 41 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 99 (Polychromatic418967fa.accept_13_10_2_8_1_2603 36 41 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 99 (Polychromatic418967fa.accept_10_5_1_9_1_791 35
  41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 99 (accept_3_4 34 41 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 99 (Polychromatic418967fa.accept_7_5_6_1_1_407 33
  41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 99
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 99 (accept_3_4 31 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 41
  99 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 41 99 (Polychromatic418967fa.accept_36_29_5_27_1_4245 29 41 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 99 (accept_3_4 28 41 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 41 99 (Polychromatic418967fa.accept_17_10_7_14_1_4244 27 41 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 26
  41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 99 (accept_3_4 25 41 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 99 (Polychromatic418967fa.accept_22_2_19_11_1_4243
  24 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 99
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 99 (accept_3_4 22 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 41
  99 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 41 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 41 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 99 (accept_3_4 19 41 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 41 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 41 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 99 (Polychromatic418967fa.accept_15_2_11_9_1_263
  17 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 99 (accept_3_4 16 41
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 99 (Polychromatic418967fa.accept_10_5_1_9_1_791
  15 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 99
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 99 (accept_3_4 13 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 41
  99 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 41 99 (Polychromatic418967fa.accept_19_11_3_4_1_4242 11 41 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 99 (accept_3_4 10 41 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 41 99 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 41 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 41
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 99 (accept_3_4 7 41 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 41
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 99
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 99 (accept_3_4 4 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41 99
  (Polychromatic418967fa.accept_22_3_19_11_1_1512 3 41 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 41 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 99 (accept_3_4 1 41 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 99))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 99 (allA_succ_of_accept 39 40 99
  (Polychromatic418967fa.accept_7_4_5_1_1_418 39 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 99 (accept_3_5 38 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 40
  99 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 40 99 (Polychromatic418967fa.accept_16_4_8_3_1_4206 36 40 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 40 99 (accept_3_5 35 40 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 40 99 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 40 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 99 (Polychromatic418967fa.accept_13_7_1_8_1_1778
  33 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 40 99 (accept_3_5 32 40
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 40 99 (Polychromatic418967fa.accept_6_1_4_3_1_14
  31 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 40 99
  (Polychromatic418967fa.accept_12_6_4_3_1_361 30 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 40 99 (accept_3_5 29 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 40
  99 (Polychromatic418967fa.accept_16_12_8_3_1_4241 28 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 40 99 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 40 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 40 99 (accept_3_5 26 40 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 40 99 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 40 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 40 99
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 40 99 (accept_3_5 23 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 40
  99 (Polychromatic418967fa.accept_13_9_1_8_1_1742 22 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 40 99 (Polychromatic418967fa.accept_16_5_8_3_1_4240 21 40 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 40 99 (accept_3_5 20 40 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 40 99 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 40 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 40 99 (Polychromatic418967fa.accept_7_4_5_1_1_418 18
  40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 99 (accept_3_5 17 40 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 40 99 (Polychromatic418967fa.accept_15_1_10_9_1_1495
  16 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 40 99
  (Polychromatic418967fa.accept_17_15_6_14_1_4239 15 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 40 99 (accept_3_5 14 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 40
  99 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 40 99 (Polychromatic418967fa.accept_13_12_1_8_1_1779 12 40 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 40 99 (accept_3_5 11 40 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 40 99 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 40 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 40 99 (Polychromatic418967fa.accept_13_9_1_8_1_1742 9
  40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 40 99 (accept_3_5 8 40 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40 99 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 40
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 40 99
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 40 99 (accept_3_5 5 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 40 99
  (Polychromatic418967fa.accept_7_4_5_1_1_418 4 40 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 40 99 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 40 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 40 99 (accept_3_5 2 40 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 40 99 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 40 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40 99)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 99
  (allA_succ_of_accept 38 39 99 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 39 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 99 (Polychromatic418967fa.accept_18_1_3_9_1_328 37 39 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 99 3 12 13 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 99
  (Polychromatic418967fa.accept_19_16_1_4_1_4235 35 39 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 39 99 (Polychromatic418967fa.accept_19_15_1_4_1_4238 34 39 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 39 99 3 11 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 39 99 (Polychromatic418967fa.accept_14_4_11_1_1_940 32 39 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 99
  (Polychromatic418967fa.accept_7_3_4_1_1_71 31 39 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 39 99 3 10 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 39 99 (Polychromatic418967fa.accept_19_10_1_4_1_4237 29 39 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 99 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 39 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 99 3 9 13 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 99
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 39 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 99 (Polychromatic418967fa.accept_16_9_7_3_1_614 25 39 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 39 99 3 8 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 39 99 (Polychromatic418967fa.accept_21_2_18_15_1_4236 23 39 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 99
  (Polychromatic418967fa.accept_19_3_1_4_1_1860 22 39 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 39 99 3 7 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 39 99 (Polychromatic418967fa.accept_8_4_7_3_1_144 20 39 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 99 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 39 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 99 3 6 13 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 99
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 39 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 39 99 (Polychromatic418967fa.accept_19_16_1_4_1_4235 16 39 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 39 99 3 5 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 39 99 (Polychromatic418967fa.accept_18_14_3_9_1_4234 14 39 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 99
  (Polychromatic418967fa.accept_18_13_3_9_1_4233 13 39 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 39 99 3 4 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 39 99 (Polychromatic418967fa.accept_16_11_7_3_1_3163 11 39 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 99 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 39 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 99 3 3 13 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 99
  (Polychromatic418967fa.accept_18_8_3_9_1_4232 8 39 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 99 (Polychromatic418967fa.accept_18_7_3_9_1_1020 7 39 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 39 99 3 2 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 39 99 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 39 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 99
  (Polychromatic418967fa.accept_8_4_7_3_1_144 4 39 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 39 99 3 1 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 39 99 (Polychromatic418967fa.accept_17_2_5_14_1_2068 2 39 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 99 (Polychromatic418967fa.accept_18_1_3_9_1_328 1 39 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 99)))))))))))))))))))))))))))))))))))))))
  (allB_succ 38 99 (allA_succ_of_accept 37 38 99 (accept_3_4 37 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 38 99 (Polychromatic418967fa.accept_13_10_12_8_1_2550 36 38 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 38 99 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 38 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 99 (accept_3_4 34 38 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 38
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 99
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 99 (accept_3_4 31 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 38
  99 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 38 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 38 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 99 (accept_3_4 28 38 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 38 99 (Polychromatic418967fa.accept_10_7_8_9_1_785 27 38 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 99 (Polychromatic418967fa.accept_7_5_3_1_1_424 26
  38 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 38 99 (accept_3_4 25 38 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 38 99 (Polychromatic418967fa.accept_10_4_8_9_1_784 24
  38 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 38 99
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 38 99 (accept_3_4 22 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 38
  99 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 38 99 (Polychromatic418967fa.accept_13_7_12_8_1_199 20 38 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 38 99 (accept_3_4 19 38 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 38 99 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 38 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 38 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 38
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 99 (accept_3_4 16 38 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 99 (Polychromatic418967fa.accept_22_15_16_11_1_546
  15 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 99
  (Polychromatic418967fa.accept_10_4_8_9_1_784 14 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 99 (accept_3_4 13 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 38
  99 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 38 99 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 38 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 99 (accept_3_4 10 38 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 38 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 38 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 99 (Polychromatic418967fa.accept_21_8_17_15_1_2834
  8 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 38 99 (accept_3_4 7 38 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38 99 (Polychromatic418967fa.accept_12_6_2_3_1_354 6
  38 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 38 99
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 38 99 (accept_3_4 4 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 38 99
  (Polychromatic418967fa.accept_15_3_8_9_1_795 3 38 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 38 99 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 38 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 99 (accept_3_4 1 38 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 38 99)))))))))))))))))))))))))))))))))))))) (allB_succ 37 99 (allA_succ_of_accept 36 37 99
  (Polychromatic418967fa.accept_13_10_11_8_1_1770 36 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 99 (accept_3_5 35 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 37
  99 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 37 99 (Polychromatic418967fa.accept_12_9_1_3_1_350 33 37 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 99 (accept_3_5 32 37 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 37 99 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 37 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 30
  37 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 99 (accept_3_5 29 37 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 37 99 (Polychromatic418967fa.accept_6_4_1_3_1_77 28
  37 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 99
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 37 99 (accept_3_5 26 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37
  99 (Polychromatic418967fa.accept_27_25_10_18_1_4231 25 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 37 99 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 37 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 99 (accept_3_5 23 37 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 37 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 37 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 99
  (Polychromatic418967fa.accept_12_9_1_3_1_350 21 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 37 99 (accept_3_5 20 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 37
  99 (Polychromatic418967fa.accept_13_6_11_8_1_1111 19 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 37 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 37 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 99 (accept_3_5 17 37 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 37 99 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 37 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 99
  (Polychromatic418967fa.accept_17_15_3_14_1_4230 15 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 37 99 (accept_3_5 14 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 37
  99 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 37 99 (Polychromatic418967fa.accept_10_2_7_9_1_783 12 37 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 99 (accept_3_5 11 37 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 37 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 37 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 99 (Polychromatic418967fa.accept_12_9_1_3_1_350 9
  37 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 99 (accept_3_5 8 37 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 99 (Polychromatic418967fa.accept_20_7_17_19_1_4229
  7 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 99
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 99 (accept_3_5 5 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37 99
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 37 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 99 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 37 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 99 (accept_3_5 2 37 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 99 (Polychromatic418967fa.accept_13_1_11_8_1_2562 1 37 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 99))))))))))))))))))))))))))))))))))))) (allB_succ 36 99
  (allA_succ_of_accept 35 36 99 (Polychromatic418967fa.accept_10_5_6_9_1_2235 35 36 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 36 99 (Polychromatic418967fa.accept_15_4_6_9_1_2269 34 36 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 36 99 3 11 12 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 36 99
  (Polychromatic418967fa.accept_19_13_17_4_1_4228 32 36 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 36 99 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 36 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 99 3 10 12 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 99 (Polychromatic418967fa.accept_15_14_6_9_1_2274 29 36 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 99
  (Polychromatic418967fa.accept_13_2_10_8_1_1126 28 36 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 36 99 9 3 4 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 36 99 (Polychromatic418967fa.accept_15_11_6_9_1_3236 26 36 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 99 (Polychromatic418967fa.accept_10_5_6_9_1_2235 25 36 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 99 3 8 12 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 99
  (Polychromatic418967fa.accept_8_7_4_3_1_156 23 36 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 36 99 (Polychromatic418967fa.accept_16_6_4_3_1_2189 22 36 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 36 99 3 7 12 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 36 99 (Polychromatic418967fa.accept_13_7_10_8_1_567 20 36 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 99
  (Polychromatic418967fa.accept_15_4_6_9_1_2269 19 36 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 99 9 2 4 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 99 (Polychromatic418967fa.accept_13_4_10_8_1_1817 17 36 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 36 99 (Polychromatic418967fa.accept_14_2_8_1_1_1647 16 36 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 36 99 3 5 12 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 36 99
  (Polychromatic418967fa.accept_15_14_6_9_1_2274 14 36 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 36 99 (Polychromatic418967fa.accept_10_3_6_9_1_779 13 36 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 99 3 4 12 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 99 (Polychromatic418967fa.accept_13_11_10_8_1_1804 11 36 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 36 99
  (Polychromatic418967fa.accept_19_10_17_4_1_4227 10 36 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 36 99 9 1 4 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 36 99 (Polychromatic418967fa.accept_16_8_4_3_1_3146 8 36 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 99 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 36 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 99 3 2 12 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 99
  (Polychromatic418967fa.accept_10_5_6_9_1_2235 5 36 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 36 99 (Polychromatic418967fa.accept_13_4_10_8_1_1817 4 36 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 36 99 3 1 12 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 36 99 (Polychromatic418967fa.accept_13_2_10_8_1_1126 2 36 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 99
  (Polychromatic418967fa.accept_15_1_6_9_1_254 1 36 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 36 99)))))))))))))))))))))))))))))))))))) (allB_succ 35 99 (allA_succ_of_accept 34 35 99 (accept_3_4 34 35
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 99
  (Polychromatic418967fa.accept_12_9_11_3_1_772 33 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 35 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 99 (accept_3_4 31 35 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 99 (Polychromatic418967fa.accept_13_4_9_8_1_1736 30 35 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 99 (Polychromatic418967fa.accept_13_3_9_8_1_4202
  29 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 99 (accept_3_4 28 35
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 99
  (Polychromatic418967fa.accept_13_1_9_8_1_1734 27 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 35 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 35 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 99 (accept_3_4 25 35 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 35 99 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 35 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 99 (Polychromatic418967fa.accept_24_23_11_3_1_4226
  23 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 99 (accept_3_4 22 35
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 99 (Polychromatic418967fa.accept_10_1_5_9_1_157
  21 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 35 99
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 35 99 (accept_3_4 19 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 35
  99 (Polychromatic418967fa.accept_15_3_5_9_1_764 18 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 35 99 (Polychromatic418967fa.accept_13_4_9_8_1_1736 17 35 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 99 (accept_3_4 16 35 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 35 99 (Polychromatic418967fa.accept_18_15_17_9_1_4200 15 35 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 35 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 14
  35 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 99 (accept_3_4 13 35 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 99 (Polychromatic418967fa.accept_13_12_9_8_1_2595
  12 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 99
  (Polychromatic418967fa.accept_10_1_5_9_1_157 11 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 35 99 (accept_3_4 10 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 35
  99 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 35 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 35 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 99 (accept_3_4 7 35 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 35 99 (Polychromatic418967fa.accept_10_6_5_9_1_1233 6 35 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 99 (Polychromatic418967fa.accept_20_5_15_19_1_4225
  5 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 99 (accept_3_4 4 35 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 99 (Polychromatic418967fa.accept_13_3_9_8_1_4202 3
  35 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 99
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 99 (accept_3_4 1 35 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  99))))))))))))))))))))))))))))))))))) (allB_succ 34 99 (allA_succ_of_accept 33 34 99
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 34 99 (accept_3_5 32 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 34
  99 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 34 99 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 34 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 99 (accept_3_5 29 34 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 34 99 (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 34 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 99 (Polychromatic418967fa.accept_15_12_4_9_1_3204
  27 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 34 99 (accept_3_5 26 34
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 34 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 25
  34 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 34 99
  (Polychromatic418967fa.accept_19_5_15_4_1_4224 24 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 34 99 (accept_3_5 23 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 34
  99 (Polychromatic418967fa.accept_16_6_2_3_1_4223 22 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 34 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 34 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 34 99 (accept_3_5 20 34 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 34 99 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 34 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 34 99 (Polychromatic418967fa.accept_10_8_4_9_1_1229
  18 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 99 (accept_3_5 17 34
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 99 (Polychromatic418967fa.accept_7_2_6_1_1_73
  16 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 99
  (Polychromatic418967fa.accept_10_5_4_9_1_420 15 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 99 (accept_3_5 14 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 34
  99 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 34 99 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 34 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 99 (accept_3_5 11 34 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 34 99 (Polychromatic418967fa.accept_15_10_4_9_1_3203 10 34 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 34
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 34 99 (accept_3_5 8 34 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34 99 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 34
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 34 99
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 34 99 (accept_3_5 5 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 34 99
  (Polychromatic418967fa.accept_20_4_14_19_1_4222 4 34 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 34 99 (Polychromatic418967fa.accept_10_3_4_9_1_15 3 34 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 99 (accept_3_5 2 34 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 34 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 34 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 99)))))))))))))))))))))))))))))))))) (allB_succ 33 99
  (allA_succ_of_accept 32 33 99 (Polychromatic418967fa.accept_7_4_5_1_1_418 32 33 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 99 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 33 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 33 99 3 10 11 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 33 99
  (Polychromatic418967fa.accept_12_5_9_3_1_85 29 33 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 33 99 (Polychromatic418967fa.accept_13_2_7_8_1_4221 28 33 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 33 99 3 9 11 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 33 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 33 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 99
  (Polychromatic418967fa.accept_7_4_5_1_1_418 25 33 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 33 99 3 8 11 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 33 99 (Polychromatic418967fa.accept_12_11_9_3_1_792 23 33 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 33 99 11 2 3 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 33 99 3 7 11 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 33 99 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 33 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 99
  (Polychromatic418967fa.accept_12_7_9_3_1_767 19 33 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 33 99 3 6 11 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 33 99 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 33 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 99 (Polychromatic418967fa.accept_10_6_3_9_1_1207 16 33 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 99 3 5 11 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 99
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 33 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 99 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 33 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 33 99 3 4 11 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 33 99 11 1 3 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 33 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 33 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 33 99 3 3 11 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 33 99
  (Polychromatic418967fa.accept_15_8_3_9_1_4220 8 33 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 99 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 33 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 99 3 2 11 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 99 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 33 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 99
  (Polychromatic418967fa.accept_7_4_5_1_1_418 4 33 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 33 99 3 1 11 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 33 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 33 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 99 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 33 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 99)))))))))))))))))))))))))))))))))
  (allB_succ 32 99 (allA_succ_of_accept 31 32 99 (accept_3_4 31 32 99 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 32 99 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 32 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 32 99 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 32 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 99 (accept_3_4 28 32 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 32 99 (Polychromatic418967fa.accept_10_7_2_9_1_775 27
  32 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 99
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 32 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 32 99 (accept_3_4 25 32 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 32
  99 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 32 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 32 99 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 32 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 99 (accept_3_4 22 32 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 32 99 (Polychromatic418967fa.accept_10_1_2_9_1_152 21 32 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 99 (Polychromatic418967fa.accept_17_3_15_14_1_4219
  20 32 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 32 99 (accept_3_4 19 32
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 32 99 (Polychromatic418967fa.accept_12_6_8_3_1_82
  18 32 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 32 99
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 32 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 32 99 (accept_3_4 16 32 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 32
  99 (Polychromatic418967fa.accept_13_2_6_8_1_1092 15 32 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 32 99 (Polychromatic418967fa.accept_13_1_6_8_1_208 14 32 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 32 99 (accept_3_4 13 32 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 32 99 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 32 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 32 99 (Polychromatic418967fa.accept_6_5_2_3_1_81 11
  32 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 99 (accept_3_4 10 32 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 99 (Polychromatic418967fa.accept_19_9_13_4_1_2982 9
  32 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 99
  (Polychromatic418967fa.accept_15_8_2_9_1_3200 8 32 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 99 (accept_3_4 7 32 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32 99
  (Polychromatic418967fa.accept_12_6_8_3_1_82 6 32 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 32 99 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 32 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 99 (accept_3_4 4 32 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 32 99 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 32 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 99 (Polychromatic418967fa.accept_13_2_6_8_1_1092 2
  32 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 99 (accept_3_4 1 32 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 99)))))))))))))))))))))))))))))))) (allB_succ 31 99
  (allA_succ_of_accept 30 31 99 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 31 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 99 (accept_3_5 29 31 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 99 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 31 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 99 (Polychromatic418967fa.accept_13_1_5_8_1_207 27
  31 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 99 (accept_3_5 26 31 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 99 (Polychromatic418967fa.accept_7_4_3_1_1_87 25
  31 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 99
  (Polychromatic418967fa.accept_18_6_13_9_1_4218 24 31 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 99 (accept_3_5 23 31 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 31
  99 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 31 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 31 99 (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 31 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 99 (accept_3_5 20 31 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 31 99 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 31 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 99 (Polychromatic418967fa.accept_7_4_3_1_1_87 18
  31 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 99 (accept_3_5 17 31 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 31 99 (Polychromatic418967fa.accept_6_4_1_3_1_77 16
  31 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 99
  (Polychromatic418967fa.accept_10_5_1_9_1_791 15 31 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 31 99 (accept_3_5 14 31 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 31
  99 (Polychromatic418967fa.accept_16_13_15_3_1_4196 13 31 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 31 99 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 31 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 99 (accept_3_5 11 31 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 31 99 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 31 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 99
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 31 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 31 99 (accept_3_5 8 31 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 99
  (Polychromatic418967fa.accept_15_7_1_9_1_1500 7 31 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 31 99 (Polychromatic418967fa.accept_15_6_1_9_1_1476 6 31 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 31 99 (accept_3_5 5 31 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 31 99 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 31 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 31 99 (Polychromatic418967fa.accept_13_3_5_8_1_1099 3
  31 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 99 (accept_3_5 2 31 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 99 (Polychromatic418967fa.accept_13_1_5_8_1_207 1
  31 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 99)))))))))))))))))))))))))))))))
  (allB_succ 30 99 (allA_succ_of_accept 29 30 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 30 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 30 99 (Polychromatic418967fa.accept_12_4_6_3_1_332 28
  30 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 30 99 3 9 10 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 30 99
  (Polychromatic418967fa.accept_12_2_6_3_1_331 26 30 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 30 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 30 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 99 3 8 10 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 99 (Polychromatic418967fa.accept_13_10_4_8_1_2570 23 30 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 99
  (Polychromatic418967fa.accept_12_10_6_3_1_786 22 30 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 30 99 3 7 10 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 30 99 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 30 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 99 (Polychromatic418967fa.accept_21_19_9_15_1_4217 19 30 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 99 3 6 10 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 99
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 30 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 30 99 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 30 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 30 99 3 5 10 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 30 99 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 30 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 99
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 30 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 30 99 3 4 10 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 30 99 (Polychromatic418967fa.accept_13_11_4_8_1_1098 11 30 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 30 99 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 30 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 30 99 3 3 10 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 30 99
  (Polychromatic418967fa.accept_12_8_6_3_1_366 8 30 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 30 99 (Polychromatic418967fa.accept_19_7_11_4_1_1872 7 30 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 99 3 2 10 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 30 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30 99
  (Polychromatic418967fa.accept_12_4_6_3_1_332 4 30 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 30 99 3 1 10 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 30 99 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 30 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 30 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 99)))))))))))))))))))))))))))))) (allB_succ
  29 99 (allA_succ_of_accept 28 29 99 (accept_3_4 28 29 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 29 99 (Polychromatic418967fa.accept_15_12_14_9_1_778 27 29 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 29 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 29 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 99 (accept_3_4 25 29 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 29 99 (Polychromatic418967fa.accept_13_11_3_8_1_1786 24 29 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 99
  (Polychromatic418967fa.accept_15_8_14_9_1_4216 23 29 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 99 (accept_3_4 22 29 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29
  99 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 29 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 29 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 29 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 99 (accept_3_4 19 29 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 29 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 29 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 99 (Polychromatic418967fa.accept_16_1_13_3_1_2168
  17 29 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 99 (accept_3_4 16 29
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 99
  (Polychromatic418967fa.accept_16_15_13_3_1_4215 15 29 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 29 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 29 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 99 (accept_3_4 13 29 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 29 99 (Polychromatic418967fa.accept_15_12_14_9_1_778 12 29 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 99 (Polychromatic418967fa.accept_13_11_3_8_1_1786
  11 29 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 99 (accept_3_4 10 29
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 99 (Polychromatic418967fa.accept_12_9_5_3_1_782
  9 29 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 99
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 29 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 29 99 (accept_3_4 7 29 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 99
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 29 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 29 99 (Polychromatic418967fa.accept_13_5_3_8_1_1117 5 29 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 99 (accept_3_4 4 29 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 29 99 (Polychromatic418967fa.accept_20_3_9_19_1_4214 3 29 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 29
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 99 (accept_3_4 1 29 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29 99))))))))))))))))))))))))))))) (allB_succ 28 99
  (allA_succ_of_accept 27 28 99 (Polychromatic418967fa.accept_10_7_8_9_1_785 27 28 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 28 99 (accept_3_5 26 28 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 28 99 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 28 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 28 99 (Polychromatic418967fa.accept_10_4_8_9_1_784 24
  28 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 99 (accept_3_5 23 28 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 99 (Polychromatic418967fa.accept_15_7_13_9_1_1466
  22 28 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 28 99
  (Polychromatic418967fa.accept_10_1_8_9_1_787 21 28 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 28 99 (accept_3_5 20 28 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 28
  99 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 28 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 28 99 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 28 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 28 99 (accept_3_5 17 28 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 28 99 (Polychromatic418967fa.accept_17_16_11_14_1_4213 16 28 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 28 99
  (Polychromatic418967fa.accept_8_7_4_3_1_156 15 28 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 28 99 (accept_3_5 14 28 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 28
  99 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 28 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 28 99 (Polychromatic418967fa.accept_17_12_11_14_1_3120 12 28 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 28 99 (accept_3_5 11 28 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 28 99 (Polychromatic418967fa.accept_13_10_2_8_1_2603 10 28 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 28 99 (Polychromatic418967fa.accept_16_9_12_3_1_3138 9
  28 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 28 99 (accept_3_5 8 28 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 28 99 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 28
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 28 99
  (Polychromatic418967fa.accept_12_6_4_3_1_361 6 28 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 28 99 (accept_3_5 5 28 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 28 99
  (Polychromatic418967fa.accept_10_4_8_9_1_784 4 28 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 28 99 (Polychromatic418967fa.accept_15_3_13_9_1_3196 3 28 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 99 (accept_3_5 2 28 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 28 99 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 28 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 99)))))))))))))))))))))))))))) (allB_succ 27 99
  (allA_succ_of_accept 26 27 99 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 27 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 99 (Polychromatic418967fa.accept_13_12_1_8_1_1779 25 27 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 27 99 3 8 9 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 27 99
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 27 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 27 99 (Polychromatic418967fa.accept_10_2_7_9_1_783 22 27 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 27 99 3 7 9 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 27 99 (Polychromatic418967fa.accept_13_7_1_8_1_1778 20 27 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 99
  (Polychromatic418967fa.accept_7_5_6_1_1_407 19 27 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 27 99 9 2 3 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 27 99 (Polychromatic418967fa.accept_19_17_8_4_1_4212 17 27 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 99 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 27 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 27 99 3 5 9 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 27 99
  (Polychromatic418967fa.accept_15_14_12_9_1_3216 14 27 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 99 (Polychromatic418967fa.accept_17_13_10_14_1_4211 13 27 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 27 99 3 4 9 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 27 99 (Polychromatic418967fa.accept_13_11_1_8_1_1776 11 27 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 99
  (Polychromatic418967fa.accept_15_10_12_9_1_776 10 27 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 27 99 9 1 3 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 27 99 (Polychromatic418967fa.accept_10_8_7_9_1_425 8 27 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 99 (Polychromatic418967fa.accept_13_7_1_8_1_1778 7 27 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 27 99 3 2 9 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 27 99
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 27 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 27 99 (Polychromatic418967fa.accept_15_4_12_9_1_773 4 27 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 27 99 3 1 9 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 27 99 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 27 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 99
  (Polychromatic418967fa.accept_17_1_10_14_1_1173 1 27 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 27 99))))))))))))))))))))))))))) (allB_succ 26 99 (allA_succ_of_accept 25 26 99 (accept_3_4 25 26 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 99 (Polychromatic418967fa.accept_7_3_5_1_1_72 24
  26 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 26 99
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 26 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 26 99 (accept_3_4 22 26 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 26
  99 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 26 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 26 99 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 26 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 99 (accept_3_4 19 26 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 26 99 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 26 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 26 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 26
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 99 (accept_3_4 16 26 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 26 99 (Polychromatic418967fa.accept_10_5_6_9_1_2235
  15 26 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 99
  (Polychromatic418967fa.accept_19_14_7_4_1_4210 14 26 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 26 99 (accept_3_4 13 26 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 26
  99 (Polychromatic418967fa.accept_16_12_10_3_1_4209 12 26 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 26 99 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 26 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 26 99 (accept_3_4 10 26 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 26 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 26 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 99
  (Polychromatic418967fa.accept_21_8_5_15_1_4208 8 26 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 26 99 (accept_3_4 7 26 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26 99
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 26 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 26 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 26 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 99 (accept_3_4 4 26 99 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 26 99 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 26 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 99 (Polychromatic418967fa.accept_15_2_11_9_1_263 2 26 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 99 (accept_3_4 1 26 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 26 99)))))))))))))))))))))))))) (allB_succ 25 99 (allA_succ_of_accept 24 25
  99 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 25 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 99 (accept_3_5 23 25 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 25
  99 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 25 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 25 99 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 25 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 99 (accept_3_5 20 25 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 25 99 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 25 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 18
  25 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 99 (accept_3_5 17 25 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 25 99 (Polychromatic418967fa.accept_6_4_1_3_1_77 16
  25 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 25 99
  (Polychromatic418967fa.accept_19_15_6_4_1_2994 15 25 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 25 99 (accept_3_5 14 25 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 25
  99 (Polychromatic418967fa.accept_19_13_6_4_1_4207 13 25 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 25 99 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 25 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 99 (accept_3_5 11 25 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 25 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 25 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 25 99
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 25 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 25 99 (accept_3_5 8 25 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 99
  (Polychromatic418967fa.accept_13_7_12_8_1_199 7 25 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 25 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 25 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 25 99 (accept_3_5 5 25 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 25 99 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 25 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 99 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 25
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 99 (accept_3_5 2 25 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 99 (Polychromatic418967fa.accept_10_1_5_9_1_157 1
  25 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 99))))))))))))))))))))))))) (allB_succ
  24 99 (allA_succ_of_accept 23 24 99 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 24 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 99 (Polychromatic418967fa.accept_13_9_11_8_1_195 22 24 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 24 99 3 7 8 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 24 99
  (Polychromatic418967fa.accept_16_4_8_3_1_4206 20 24 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 24 99 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 24 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 99 3 6 8 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 99 (Polychromatic418967fa.accept_13_4_11_8_1_1768 17 24 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 99
  (Polychromatic418967fa.accept_7_2_3_1_1_10 16 24 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 24 99 3 5 8 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 24 99 (Polychromatic418967fa.accept_13_1_11_8_1_2562 14 24 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 99 (Polychromatic418967fa.accept_10_3_4_9_1_15 13 24 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 99 3 4 8 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 99
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 24 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 24 99 (Polychromatic418967fa.accept_13_10_11_8_1_1770 10 24 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 24 99 3 3 8 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 24 99 (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 24 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 99
  (Polychromatic418967fa.accept_18_7_6_9_1_4205 7 24 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 24 99 3 2 8 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 24 99 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 24 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 99 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 24 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 24 99 3 1 8 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 24 99
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 24 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 24 99 (Polychromatic418967fa.accept_13_1_11_8_1_2562 1 24 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 24 99)))))))))))))))))))))))) (allB_succ 23 99 (allA_succ_of_accept 22 23 99
  (accept_3_4 22 23 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 99
  (Polychromatic418967fa.accept_12_9_11_3_1_772 21 23 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 23 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 99 (accept_3_4 19 23 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 99 (Polychromatic418967fa.accept_13_5_10_8_1_1127 18 23 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 99 (Polychromatic418967fa.accept_7_3_2_1_1_225 17
  23 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 99 (accept_3_4 16 23 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 99 (Polychromatic418967fa.accept_13_2_10_8_1_1126
  15 23 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 99
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 23 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 99 (accept_3_4 13 23 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 23
  99 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 23 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 23 99 (Polychromatic418967fa.accept_13_11_10_8_1_1804 11 23 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 99 (accept_3_4 10 23 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 23 99 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 23 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 23
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 99 (accept_3_4 7 23 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 99 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 23
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 99
  (Polychromatic418967fa.accept_13_5_10_8_1_1127 5 23 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 99 (accept_3_4 4 23 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23 99
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 23 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 23 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 23 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 99 (accept_3_4 1 23 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 23 99))))))))))))))))))))))) (allB_succ 22 99 (allA_succ_of_accept 21 22 99
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 22 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 99 (accept_3_5 20 22 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 22
  99 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 22 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 22 99 (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 22 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 99 (accept_3_5 17 22 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 22 99 (Polychromatic418967fa.accept_13_3_9_8_1_4202 16 22 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 99 (Polychromatic418967fa.accept_18_15_4_9_1_4204
  15 22 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 22 99 (accept_3_5 14 22
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 22 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 13
  22 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 22 99
  (Polychromatic418967fa.accept_13_12_9_8_1_2595 12 22 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 11 22 99 11 1 2 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 10 22 99 (Polychromatic418967fa.accept_17_10_5_14_1_4203 10 22 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 22 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 22 99 (accept_3_5 8 22 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22 99 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 22 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 22 99
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 22 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 22 99 (accept_3_5 5 22 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 22 99
  (Polychromatic418967fa.accept_13_4_9_8_1_1736 4 22 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 22 99 (Polychromatic418967fa.accept_13_3_9_8_1_4202 3 22 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 99 (accept_3_5 2 22 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 22 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 22 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 99)))))))))))))))))))))) (allB_succ 21 99 (allA_succ_of_accept
  20 21 99 (Polychromatic418967fa.accept_14_6_7_1_1_78 20 21 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 21 99 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 21 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 99 3 6 7 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 99 (Polychromatic418967fa.accept_12_5_9_3_1_85 17
  21 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 99
  (Polychromatic418967fa.accept_15_1_6_9_1_254 16 21 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 21 99 3 5 7 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 21 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 21 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 99 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 21 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 21 99 3 4 7 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 21 99
  (Polychromatic418967fa.accept_12_11_9_3_1_792 11 21 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 21 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 99 3 3 7 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 99 (Polychromatic418967fa.accept_10_8_1_9_1_413 8 21 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 99
  (Polychromatic418967fa.accept_12_7_9_3_1_767 7 21 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 21 99 3 2 7 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 21 99 (Polychromatic418967fa.accept_10_5_1_9_1_791 5 21 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 99 (Polychromatic418967fa.accept_15_4_6_9_1_2269 4 21 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 21 99 3 1 7 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 21 99
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 21 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 21 99 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 21 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 21 99))))))))))))))))))))) (allB_succ 20 99 (allA_succ_of_accept 19 20 99
  (accept_3_4 19 20 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 99
  (Polychromatic418967fa.accept_12_6_8_3_1_82 18 20 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 20 99 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 20 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 99 (accept_3_4 16 20 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 20 99 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 20 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 20 99 (Polychromatic418967fa.accept_13_1_7_8_1_1796
  14 20 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 99 (accept_3_4 13 20
  99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 99 (Polychromatic418967fa.accept_7_5_6_1_1_407
  12 20 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 20 99
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 20 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 20 99 (accept_3_4 10 20 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 20
  99 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 20 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 20 99 (Polychromatic418967fa.accept_16_8_4_3_1_3146 8 20 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 99 (accept_3_4 7 20 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 20 99 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 20 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 20 99 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 20
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 20 99 (accept_3_4 4 20 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20 99 (Polychromatic418967fa.accept_13_3_7_8_1_4192 3
  20 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 20 99
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 20 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 20 99 (accept_3_4 1 20 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20
  99)))))))))))))))))))) (allB_succ 19 99 (allA_succ_of_accept 18 19 99 (Polychromatic418967fa.accept_7_4_5_1_1_418 18
  19 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 19 99 (accept_3_5 17 19 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 19 99 (Polychromatic418967fa.accept_6_4_1_3_1_77 16
  19 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 19 99
  (Polychromatic418967fa.accept_13_2_6_8_1_1092 15 19 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 19 99 (accept_3_5 14 19 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 19
  99 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 19 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 19 99 (Polychromatic418967fa.accept_15_12_4_9_1_3204 12 19 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 19 99 (accept_3_5 11 19 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 19 99 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 19 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 19 99 (Polychromatic418967fa.accept_12_9_7_3_1_1309 9
  19 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 99 (accept_3_5 8 19 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 99 (Polychromatic418967fa.accept_21_7_19_15_1_4201
  7 19 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 99
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 19 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 99 (accept_3_5 5 19 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19 99
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 19 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 99 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 19 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 99 (accept_3_5 2 19 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 99 (Polychromatic418967fa.accept_13_1_6_8_1_208 1 19 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 99))))))))))))))))))) (allB_succ 18 99 (allA_succ_of_accept 17
  18 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 18 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 18 99 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 18 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 18 99 3 5 6 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 18 99 (Polychromatic418967fa.accept_10_4_8_9_1_784 14 18 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 18 99
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 18 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 18 99 3 4 6 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 18 99 (Polychromatic418967fa.accept_10_1_8_9_1_787 11 18 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 99 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 18 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 18 99 9 1 2 11 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 18 99
  (Polychromatic418967fa.accept_12_8_6_3_1_366 8 18 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 99 (Polychromatic418967fa.accept_10_7_8_9_1_785 7 18 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 99 3 2 6 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 18 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 99
  (Polychromatic418967fa.accept_10_4_8_9_1_784 4 18 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 18 99 3 1 6 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 18 99 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 18 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 18 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 99)))))))))))))))))) (allB_succ 17 99
  (allA_succ_of_accept 16 17 99 (accept_3_4 16 17 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17
  99 (Polychromatic418967fa.accept_18_15_17_9_1_4200 15 17 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 17 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 17 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 99 (accept_3_4 13 17 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 17 99 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 17 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 99
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 17 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 17 99 (accept_3_4 10 17 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 17
  99 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 17 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 17 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 17 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 99 (accept_3_4 7 17 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 17 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 17 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 99 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 17
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 99 (accept_3_4 4 17 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17 99 (Polychromatic418967fa.accept_21_3_17_15_1_4199
  3 17 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 99
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 17 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 17 99 (accept_3_4 1 17 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17
  99))))))))))))))))) (allB_succ 16 99 (allA_succ_of_accept 15 16 99 (Polychromatic418967fa.accept_10_5_6_9_1_2235 15 16
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 16 99 (accept_3_5 14 16 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 16 99 (Polychromatic418967fa.accept_6_1_4_3_1_14 13
  16 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 16 99
  (Polychromatic418967fa.accept_18_12_16_9_1_4198 12 16 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 16 99 (accept_3_5 11 16 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 16
  99 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 16 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 16 99 (Polychromatic418967fa.accept_13_9_3_8_1_573 9 16 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 16 99 (accept_3_5 8 16 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 16 99 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 16 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 16 99 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 16
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 16 99 (accept_3_5 5 16 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 16 99 (Polychromatic418967fa.accept_22_4_16_11_1_4197
  4 16 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 16 99
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 16 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 16 99 (accept_3_5 2 16 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 16 99
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 16 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 16 99)))))))))))))))) (allB_succ 15 99 (allA_succ_of_accept 14 15 99
  (Polychromatic418967fa.accept_10_4_5_9_1_1231 14 15 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 99 (Polychromatic418967fa.accept_16_13_15_3_1_4196 13 15 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 99 3 4 5 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 99 (Polychromatic418967fa.accept_10_1_5_9_1_157 11 15 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 99
  (Polychromatic418967fa.accept_13_10_2_8_1_2603 10 15 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 15 99 3 3 5 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 15 99 (Polychromatic418967fa.accept_19_8_15_4_1_2953 8 15 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 99 (Polychromatic418967fa.accept_13_7_2_8_1_1746 7 15 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 15 99 3 2 5 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 15 99
  (Polychromatic418967fa.accept_18_5_15_9_1_1919 5 15 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 15 99 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 15 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 99 3 1 5 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 99 (Polychromatic418967fa.accept_16_2_15_3_1_1300 2 15 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 99
  (Polychromatic418967fa.accept_10_1_5_9_1_157 1 15 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 15 99))))))))))))))) (allB_succ 14 99 (allA_succ_of_accept 13 14 99 (accept_3_4 13 14 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 99 (Polychromatic418967fa.accept_13_12_1_8_1_1779 12 14 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 14 99
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 14 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 14 99 (accept_3_4 10 14 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 14
  99 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 14 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 14 99 (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 14 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 99 (accept_3_4 7 14 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 14 99 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 14 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 14
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 14 99 (accept_3_4 4 14 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14 99 (Polychromatic418967fa.accept_10_3_4_9_1_15 3 14
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 14 99
  (Polychromatic418967fa.accept_19_2_14_4_1_4195 2 14 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 14 99 (accept_3_4 1 14 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14
  99)))))))))))))) (allB_succ 13 99 (allA_succ_of_accept 12 13 99 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 13 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 13 99 (accept_3_5 11 13 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 13 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 10
  13 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 13 99
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 13 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 13 99 (accept_3_5 8 13 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 99
  (Polychromatic418967fa.accept_14_7_13_1_1_922 7 13 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 13 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 13 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 13 99 (accept_3_5 5 13 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 13 99 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 13 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 13 99 (Polychromatic418967fa.accept_15_3_13_9_1_3196 3
  13 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 99 (accept_3_5 2 13 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 99 (Polychromatic418967fa.accept_16_1_13_3_1_2168 1
  13 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 99))))))))))))) (allB_succ 12 99
  (allA_succ_of_accept 11 12 99 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 12 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 99 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 12 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 12 99 3 3 4 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 12 99
  (Polychromatic418967fa.accept_16_8_12_3_1_4194 8 12 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 12 99 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 12 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 99 3 2 4 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 99 (Polychromatic418967fa.accept_13_5_12_8_1_198 5 12 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 99
  (Polychromatic418967fa.accept_7_4_5_1_1_418 4 12 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 12 99 3 1 4 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 12 99 (Polychromatic418967fa.accept_19_2_12_4_1_4193 2 12 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 99 (Polychromatic418967fa.accept_10_1_2_9_1_152 1 12 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 99)))))))))))) (allB_succ 11 99
  (allA_succ_of_accept 10 11 99 (accept_3_4 10 11 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11
  99 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 11 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 99 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 11 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 99 (accept_3_4 7 11 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 99 (Polychromatic418967fa.accept_13_6_11_8_1_1111 6 11 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 99 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 11
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 99 (accept_3_4 4 11 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 99 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 11
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 99
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 11 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 99 (accept_3_4 1 11 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11 99)))))))))))
  (allB_succ 10 99 (allA_succ_of_accept 9 10 99 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 10 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 10 99 (accept_3_5 8 10 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 10 99 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 10 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 10 99 (Polychromatic418967fa.accept_12_6_10_3_1_1313 6
  10 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 10 99 (accept_3_5 5 10 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 10 99 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 10
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 10 99
  (Polychromatic418967fa.accept_15_3_10_9_1_769 3 10 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 10 99 (accept_3_5 2 10 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 10 99
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 10 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 10 99)))))))))) (allB_succ 9 99 (allA_succ_of_accept 8 9 99 (Polychromatic418967fa.accept_14_8_9_1_1_3313 8
  9 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 99
  (Polychromatic418967fa.accept_12_7_9_3_1_767 7 9 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 9 99 3 2 3 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 9 99 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 9 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 99 (Polychromatic418967fa.accept_13_4_9_8_1_1736 4 9 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 9 99 3 1 3 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 9 99
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 9 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 99 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 9 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 9 99))))))))) (allB_succ 8 99 (allA_succ_of_accept 7 8 99 (accept_3_4 7 8 99
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 99 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 8
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 8 99
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 8 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 8 99 (accept_3_4 4 8 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 8 99
  (Polychromatic418967fa.accept_15_3_8_9_1_795 3 8 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 8 99 (Polychromatic418967fa.accept_14_2_8_1_1_1647 2 8 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 99 (accept_3_4 1 8 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 8 99)))))))) (allB_succ 7 99 (allA_succ_of_accept 6 7 99
  (Polychromatic418967fa.accept_14_6_7_1_1_78 6 7 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 99 (accept_3_5 5 7 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 99
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 7 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 99 (Polychromatic418967fa.accept_13_3_7_8_1_4192 3 7 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 99 (accept_3_5 2 7 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 99 (Polychromatic418967fa.accept_13_1_7_8_1_1796 1 7 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 99))))))) (allB_succ 6 99 (allA_succ_of_accept 5 6 99
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 6 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 99 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 6 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 6 99 3 1 2 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 6 99 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 6 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 99
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 6 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 6 99)))))) (allB_succ 5 99 (allA_succ_of_accept 4 5 99 (accept_3_4 4 5 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 5 99 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 5 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 99 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 5 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 99 (accept_3_4 1 5 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 5 99))))) (allB_succ 4 99 (allA_succ_of_accept 3 4 99
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 4 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 99 (accept_3_5 2 4 99 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 99
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 4 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 99)))) (allB_succ 3 99 (allA_succ_of_accept 2 3 99 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 3 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 99
  (Polychromatic418967fa.accept_18_1_3_9_1_328 1 3 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 3 99))) (allB_succ 2 99 (allA_succ_of_accept 1 2 99 (accept_3_4 1 2 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 2 99)) (allB_two
  99)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


