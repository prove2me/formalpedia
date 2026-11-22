-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch95
-- name    : Polychromatic418967fa_Branch95
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:09:20.667915+00:00
-- url     : https://prove2.me/theorems/f8f10eb4-7fd2-4060-9427-7ad0b76e17bf
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

def Polychromatic418967fa.branch_95 : allB 95 95 :=
  allB_succ' 2 94 95 (Eq.refl Bool.true) (allA_of_3_0 2 94 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3 93
  95 (Eq.refl Bool.true) (allA_succ_of_accept 2 93 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 93 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 95 (accept_3_2 1 93 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 93 95))) (allB_succ' 4 92 95 (Eq.refl Bool.true) (allA_succ_of_accept 3 92
  95 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 92 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 92 95 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 92 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 95 (accept_3_2 1 92 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 92 95)))) (allB_succ' 5 91 95 (Eq.refl Bool.true) (allA_of_3_0 5 91 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 6 90 95 (Eq.refl Bool.true) (allA_succ_of_gcd 5 90 95 5 1 18 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 90 95 (accept_3_2 4 90 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 90 95 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 90 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 95
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 90 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 90 95 (accept_3_2 1 90 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90 95))))))
  (allB_succ' 7 89 95 (Eq.refl Bool.true) (allA_succ_of_accept 6 89 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 89
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 95
  (Polychromatic418967fa.accept_20_5_9_15_1_3973 5 89 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 95 (accept_3_2 4 89 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89 95
  (Polychromatic418967fa.accept_9_3_8_5_1_65 3 89 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 89 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 95 (accept_3_2 1 89 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 95))))))) (allB_succ' 8 88 95 (Eq.refl Bool.true) (allA_of_3_0 8 88 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 9 87 95 (Eq.refl Bool.true) (allA_succ_of_accept 8 87 95
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 87 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 95 (accept_3_2 7 87 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87 95
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 87 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 95 (Polychromatic418967fa.accept_13_5_9_4_1_441 5 87 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 95 (accept_3_2 4 87 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 87 95 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 87 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 95 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 87
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 95 (accept_3_2 1 87 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87 95))))))))) (allB_succ' 10 86 95 (Eq.refl Bool.true)
  (allA_succ_of_accept 9 86 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 86 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 95 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 86 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 86 95 (accept_3_2 7 86 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86 95 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 86 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 86 95
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 86 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 86 95 (accept_3_2 4 86 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 86 95
  (Polychromatic418967fa.accept_6_3_2_5_1_32 3 86 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 86 95 (Polychromatic418967fa.accept_11_2_9_7_1_124 2 86 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 95 (accept_3_2 1 86 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 86 95)))))))))) (allB_succ' 11 85 95 (Eq.refl Bool.true) (allA_of_3_0 11 85 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 12 84 95 (Eq.refl Bool.true) (allA_succ_of_accept 11 84 95
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 84 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 84 95 (accept_3_2 10 84 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 84
  95 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 84 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 84 95 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 84 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 95 (accept_3_2 7 84 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 84 95 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 84 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 84 95 (Polychromatic418967fa.accept_13_5_6_4_1_1582 5
  84 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84 95 (accept_3_2 4 84 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 84 95 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 84
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 84 95
  (Polychromatic418967fa.accept_9_2_3_5_1_60 2 84 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 84 95 (accept_3_2 1 84 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84 95))))))))))))
  (allB_succ' 13 83 95 (Eq.refl Bool.true) (allA_succ_of_accept 12 83 95 (Polychromatic418967fa.accept_7_5_6_4_1_117 12
  83 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 95
  (Polychromatic418967fa.accept_15_11_8_5_1_1278 11 83 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 95 (accept_3_2 10 83 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 83
  95 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 83 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 83 95 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 83 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 95 (accept_3_2 7 83 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 83 95 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 83 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 95 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 83
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 83 95 (accept_3_2 4 83 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83 95 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 83
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 95
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 83 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 83 95 (accept_3_2 1 83 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 83 95)))))))))))))
  (allB_succ' 14 82 95 (Eq.refl Bool.true) (allA_of_3_0 14 82 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 15
  81 95 (Eq.refl Bool.true) (allA_succ_of_accept 14 81 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 81 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 95 (accept_3_2 13 81 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 95 (Polychromatic418967fa.accept_13_12_3_4_1_928 12 81 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 95
  (Polychromatic418967fa.accept_15_11_6_5_1_1295 11 81 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 95 (accept_3_2 10 81 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81
  95 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 81 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 95 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 81 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 95 (accept_3_2 7 81 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 81 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 81 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 95 (Polychromatic418967fa.accept_16_5_1_15_1_3922 5
  81 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 95 (accept_3_2 4 81 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 95 (Polychromatic418967fa.accept_11_3_4_7_1_114 3
  81 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 95
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 81 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 81 95 (accept_3_2 1 81 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  95))))))))))))))) (allB_succ' 16 80 95 (Eq.refl Bool.true) (allA_succ_of_gcd 15 80 95 5 3 16 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 80 95
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 80 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 80 95 (accept_3_2 13 80 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 80
  95 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 80 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 80 95 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 80 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 80 95 5 2 16 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 80 95 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 80 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 95
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 80 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 80 95 (accept_3_2 7 80 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80 95
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 80 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 80 95 5 1 16 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 80 95 (accept_3_2 4 80 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 80 95
  (Polychromatic418967fa.accept_6_3_2_5_1_32 3 80 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 80 95 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 80 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 80 95 (accept_3_2 1 80 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 80 95)))))))))))))))) (allB_succ' 17 79 95 (Eq.refl Bool.true) (allA_of_3_0 17 79 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 18 78 95 (Eq.refl Bool.true) (allA_succ_of_accept 17 78 95
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 78 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 78 95 (accept_3_2 16 78 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 78
  95 (Polychromatic418967fa.accept_18_15_6_5_1_3972 15 78 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 78 95 (Polychromatic418967fa.accept_23_14_9_3_1_3971 14 78 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 95 (accept_3_2 13 78 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 95 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 78 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 78 95
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 78 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 78 95 (accept_3_2 10 78 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 78
  95 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 78 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 78 95 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 78 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 95 (accept_3_2 7 78 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 78 95 (Polychromatic418967fa.accept_11_6_1_7_1_1315 6 78 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 78 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 78
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78 95 (accept_3_2 4 78 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 78 95 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 78
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 95
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 78 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 78 95 (accept_3_2 1 78 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  95)))))))))))))))))) (allB_succ' 19 77 95 (Eq.refl Bool.true) (allA_succ_of_accept 18 77 95
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 77 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 77 95 (Polychromatic418967fa.accept_14_3_7_11_1_765 17 77 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 77 95 (accept_3_2 16 77 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 77 95 (Polychromatic418967fa.accept_13_2_12_4_1_943 15 77 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 77 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 14
  77 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 95 (accept_3_2 13 77 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 95 (Polychromatic418967fa.accept_10_2_7_5_1_605 12
  77 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 95
  (Polychromatic418967fa.accept_13_11_12_4_1_3945 11 77 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 95 (accept_3_2 10 77 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 77
  95 (Polychromatic418967fa.accept_25_9_2_20_1_3970 9 77 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 77 95 (Polychromatic418967fa.accept_10_8_7_5_1_602 8 77 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 95 (accept_3_2 7 77 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 77 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 77 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 95 (Polychromatic418967fa.accept_13_5_12_4_1_449 5
  77 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 77 95 (accept_3_2 4 77 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77 95 (Polychromatic418967fa.accept_10_3_7_5_1_288 3
  77 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 77 95
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 77 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 77 95 (accept_3_2 1 77 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 77
  95))))))))))))))))))) (allB_succ' 20 76 95 (Eq.refl Bool.true) (allA_of_3_0 20 76 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 21 75 95 (Eq.refl Bool.true) (allA_succ_of_gcd 20 75 95 5 4 15 19 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 75 95 (accept_3_2 19 75 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 95 (Polychromatic418967fa.accept_13_5_10_4_1_1564 18 75 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 95
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 75 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 75 95 (accept_3_2 16 75 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 95
  5 3 15 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75
  95 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 75 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 95 (accept_3_2 13 75 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 75
  95 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 75 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 75 95 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 75 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 75 95 5 2 15 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 75 95 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 75 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 95
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 75 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 95 (accept_3_2 7 75 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 95
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 75 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 75 95 5 1 15 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 75 95 (accept_3_2 4 75 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 95
  (Polychromatic418967fa.accept_16_3_11_15_1_1963 3 75 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 75 95 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 75 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 95 (accept_3_2 1 75 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 75 95))))))))))))))))))))) (allB_succ' 22 74 95 (Eq.refl Bool.true) (allA_succ_of_accept 21 74
  95 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 74 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 74 95 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 74 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 74 95 (accept_3_2 19 74 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 74 95 (Polychromatic418967fa.accept_13_5_9_4_1_441 18 74 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 74 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 74
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 95 (accept_3_2 16 74 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 74 95 (Polychromatic418967fa.accept_6_3_2_5_1_32 15
  74 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 95
  (Polychromatic418967fa.accept_16_14_10_15_1_3969 14 74 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 74 95 (accept_3_2 13 74 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 74
  95 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 74 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 74 95 (Polychromatic418967fa.accept_10_1_4_5_1_1031 11 74 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 95 (accept_3_2 10 74 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 74 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 74 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 95 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 74
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 74 95 (accept_3_2 7 74 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74 95 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 74
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 74 95
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 74 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 74 95 (accept_3_2 4 74 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 74 95
  (Polychromatic418967fa.accept_6_3_2_5_1_32 3 74 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 74 95 (Polychromatic418967fa.accept_15_2_14_5_1_2072 2 74 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 95 (accept_3_2 1 74 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 74 95)))))))))))))))))))))) (allB_succ' 23 73 95 (Eq.refl Bool.true) (allA_of_3_0 23 73 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 72 95 (Eq.refl Bool.true) (allA_succ_of_accept 23 72 95
  (Polychromatic418967fa.accept_10_3_2_5_1_295 23 72 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 95 (accept_3_2 22 72 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 72
  95 (Polychromatic418967fa.accept_15_6_12_5_1_2108 21 72 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 72 95 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 72 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 95 (accept_3_2 19 72 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 95 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 72 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 72 95
  (Polychromatic418967fa.accept_10_7_2_5_1_298 17 72 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 72 95 (accept_3_2 16 72 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 72
  95 (Polychromatic418967fa.accept_17_15_4_10_1_3968 15 72 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 72 95 (Polychromatic418967fa.accept_28_14_16_11_1_3967 14 72 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 95 (accept_3_2 13 72 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 95 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 72 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 72 95
  (Polychromatic418967fa.accept_13_11_7_4_1_1561 11 72 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 72 95 (accept_3_2 10 72 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 72
  95 (Polychromatic418967fa.accept_13_9_7_4_1_953 9 72 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 72 95 (Polychromatic418967fa.accept_10_8_2_5_1_596 8 72 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 95 (accept_3_2 7 72 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 72 95 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 72 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 72 95 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 72
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 72 95 (accept_3_2 4 72 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 72 95 (Polychromatic418967fa.accept_10_3_2_5_1_295 3
  72 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 72 95
  (Polychromatic418967fa.accept_15_2_12_5_1_2107 2 72 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 72 95 (accept_3_2 1 72 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  95)))))))))))))))))))))))) (allB_succ' 25 71 95 (Eq.refl Bool.true) (allA_succ_of_accept 24 71 95
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 71 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 71 95 (Polychromatic418967fa.accept_13_10_6_4_1_1583 23 71 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 71 95 (accept_3_2 22 71 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 71 95 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 71 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 71 95 (Polychromatic418967fa.accept_9_2_8_5_1_228 20
  71 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 95 (accept_3_2 19 71 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 95 (Polychromatic418967fa.accept_13_5_6_4_1_1582
  18 71 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 95
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 71 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 95 (accept_3_2 16 71 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 71
  95 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 71 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 71 95 (Polychromatic418967fa.accept_10_4_1_5_1_1018 14 71 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 95 (accept_3_2 13 71 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 71 95 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 71 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 95 (Polychromatic418967fa.accept_9_2_8_5_1_228 11
  71 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 71 95 (accept_3_2 10 71 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 71 95 (Polychromatic418967fa.accept_10_9_1_5_1_594 9
  71 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 95
  (Polychromatic418967fa.accept_15_8_11_5_1_169 8 71 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 71 95 (accept_3_2 7 71 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 95
  (Polychromatic418967fa.accept_9_6_8_5_1_837 6 71 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 71 95 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 71 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 71 95 (accept_3_2 4 71 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 71 95 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 71 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 95 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 71
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 95 (accept_3_2 1 71 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 71 95))))))))))))))))))))))))) (allB_succ' 26 70 95 (Eq.refl
  Bool.true) (allA_of_3_0 26 70 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 69 95 (Eq.refl Bool.true)
  (allA_succ_of_accept 26 69 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 69 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 95 (accept_3_2 25 69 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 69 95 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 69 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 95 (Polychromatic418967fa.accept_7_2_6_4_1_29 23
  69 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 95 (accept_3_2 22 69 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 95 (Polychromatic418967fa.accept_9_3_6_5_1_63 21
  69 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 95
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 69 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 95 (accept_3_2 19 69 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 69
  95 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 69 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 69 95 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 69 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 95 (accept_3_2 16 69 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 69 95 (Polychromatic418967fa.accept_11_4_3_7_1_828 15 69 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 14
  69 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 95 (accept_3_2 13 69 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 69 95 (Polychromatic418967fa.accept_7_5_6_4_1_117 12
  69 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 95
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 69 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 95 (accept_3_2 10 69 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69
  95 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 69 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 69 95 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 69 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 95 (accept_3_2 7 69 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 69 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 69 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 95 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 69
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 95 (accept_3_2 4 69 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 95 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 69
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 95
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 69 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 69 95 (accept_3_2 1 69 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  95))))))))))))))))))))))))))) (allB_succ' 28 68 95 (Eq.refl Bool.true) (allA_succ_of_accept 27 68 95
  (Polychromatic418967fa.accept_6_3_2_5_1_32 27 68 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 68 95 (Polychromatic418967fa.accept_12_2_8_11_1_31 26 68 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 68 95 (accept_3_2 25 68 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 68 95 (Polychromatic418967fa.accept_16_8_4_15_1_2941 24 68 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 68 95 (Polychromatic418967fa.accept_7_2_5_4_1_115 23
  68 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 95 (accept_3_2 22 68 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 68 95 (Polychromatic418967fa.accept_6_3_2_5_1_32 21
  68 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 95
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 68 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 68 95 (accept_3_2 19 68 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 68
  95 (Polychromatic418967fa.accept_15_3_8_5_1_2105 18 68 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 68 95 (Polychromatic418967fa.accept_10_7_8_5_1_1008 17 68 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 95 (accept_3_2 16 68 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 68 95 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 68 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 95 (Polychromatic418967fa.accept_12_2_8_11_1_31 14
  68 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 68 95 (accept_3_2 13 68 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 68 95 (Polychromatic418967fa.accept_10_2_8_5_1_587 12
  68 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 68 95
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 68 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 68 95 (accept_3_2 10 68 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 68
  95 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 68 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 68 95 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 68 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 68 95 (accept_3_2 7 68 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 68 95 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 68 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 68 95 (Polychromatic418967fa.accept_16_5_4_15_1_1102 5
  68 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 95 (accept_3_2 4 68 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 68 95 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 68
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 95
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 68 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 68 95 (accept_3_2 1 68 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  95)))))))))))))))))))))))))))) (allB_succ' 29 67 95 (Eq.refl Bool.true) (allA_of_3_0 29 67 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 30 66 95 (Eq.refl Bool.true) (allA_succ_of_accept 29 66 95
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 66 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 95 (accept_3_2 28 66 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 66
  95 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 66 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 66 95 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 66 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 95 (accept_3_2 25 66 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 66 95 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 66 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 95 (Polychromatic418967fa.accept_13_10_1_4_1_3103
  23 66 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 66 95 (accept_3_2 22 66
  95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 66 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 21
  66 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 66 95
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 66 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 66 95 (accept_3_2 19 66 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 66
  95 (Polychromatic418967fa.accept_13_5_1_4_1_3966 18 66 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 66 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 66 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 66 95 (accept_3_2 16 66 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 66 95 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 66 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 66 95 (Polychromatic418967fa.accept_10_4_6_5_1_74 14
  66 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 95 (accept_3_2 13 66 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 95 (Polychromatic418967fa.accept_15_12_6_5_1_1275
  12 66 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 95
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 66 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 95 (accept_3_2 10 66 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 66
  95 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 66 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 66 95 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 66 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 95 (accept_3_2 7 66 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 66 95 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 66 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 66
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66 95 (accept_3_2 4 66 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66 95 (Polychromatic418967fa.accept_13_3_1_4_1_945 3
  66 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 95
  (Polychromatic418967fa.accept_9_2_3_5_1_60 2 66 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 66 95 (accept_3_2 1 66 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  95)))))))))))))))))))))))))))))) (allB_succ' 31 65 95 (Eq.refl Bool.true) (allA_succ_of_gcd 30 65 95 5 6 13 19
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 65 95
  (Polychromatic418967fa.accept_20_9_5_15_1_3965 29 65 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 95 (accept_3_2 28 65 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 65
  95 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 65 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 65 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 65 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 65 95 5 5 13 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 65 95 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 65 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 95
  (Polychromatic418967fa.accept_20_3_5_15_1_2644 23 65 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 95 (accept_3_2 22 65 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 65
  95 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 65 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 65 95 5 4 13 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 65 95 (accept_3_2 19 65 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 65
  95 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 65 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 65 95 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 65 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 95 (accept_3_2 16 65 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 65 95 5 3 13 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 65 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 65 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 95 (accept_3_2 13 65 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 95 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 65 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 95
  (Polychromatic418967fa.accept_16_11_1_15_1_1123 11 65 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 65 95 5 2 13 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 65 95 (Polychromatic418967fa.accept_20_9_5_15_1_3965 9 65 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 95 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 65 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 95 (accept_3_2 7 65 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 65 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 65 95 5 1 13 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 65 95 (accept_3_2 4 65 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65 95 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 65 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 95
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 65 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 65 95 (accept_3_2 1 65 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65
  95))))))))))))))))))))))))))))))) (allB_succ' 32 64 95 (Eq.refl Bool.true) (allA_of_3_0 32 64 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 33 63 95 (Eq.refl Bool.true) (allA_succ_of_accept 32 63 95
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 63 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 95 (accept_3_2 31 63 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 63
  95 (Polychromatic418967fa.accept_18_12_9_5_1_2771 30 63 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 95 (Polychromatic418967fa.accept_20_9_3_15_1_3929 29 63 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 95 (accept_3_2 28 63 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 95 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 63 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 95
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 63 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 95 (accept_3_2 25 63 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 63
  95 (Polychromatic418967fa.accept_14_10_7_11_1_3015 24 63 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 95 (Polychromatic418967fa.accept_13_10_11_4_1_2248 23 63 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 95 (accept_3_2 22 63 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 95 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 63 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 95
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 63 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 95 (accept_3_2 19 63 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 63
  95 (Polychromatic418967fa.accept_10_8_3_5_1_613 18 63 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 63 95 (Polychromatic418967fa.accept_10_7_3_5_1_301 17 63 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 95 (accept_3_2 16 63 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 63 95 (Polychromatic418967fa.accept_11_4_8_7_1_819 15 63 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 95 (Polychromatic418967fa.accept_6_2_3_5_1_26 14
  63 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 95 (accept_3_2 13 63 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 63 95 (Polychromatic418967fa.accept_10_2_3_5_1_996 12
  63 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 95
  (Polychromatic418967fa.accept_24_11_15_23_1_3964 11 63 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 63 95 (accept_3_2 10 63 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63
  95 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 63 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 95 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 63 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 95 (accept_3_2 7 63 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 63 95 (Polychromatic418967fa.accept_13_6_11_4_1_938 6 63 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 95 (Polychromatic418967fa.accept_17_5_12_10_1_3963
  5 63 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 95 (accept_3_2 4 63 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 95 (Polychromatic418967fa.accept_14_3_7_11_1_765 3
  63 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 95
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 63 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 63 95 (accept_3_2 1 63 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  95))))))))))))))))))))))))))))))))) (allB_succ' 34 62 95 (Eq.refl Bool.true) (allA_succ_of_accept 33 62 95
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 62 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 62 95 (Polychromatic418967fa.accept_12_8_2_11_1_246 32 62 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 62 95 (accept_3_2 31 62 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 62 95 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 62 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 62 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 62
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 62 95 (accept_3_2 28 62 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 62 95 (Polychromatic418967fa.accept_6_3_2_5_1_32 27
  62 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 62 95
  (Polychromatic418967fa.accept_7_5_6_4_1_117 26 62 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 62 95 (accept_3_2 25 62 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 62
  95 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 62 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 62 95 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 62 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 62 95 (accept_3_2 22 62 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 62 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 62 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 62 95 (Polychromatic418967fa.accept_9_2_8_5_1_228 20
  62 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 62 95 (accept_3_2 19 62 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 62 95 (Polychromatic418967fa.accept_10_8_2_5_1_596 18
  62 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 62 95
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 62 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 62 95 (accept_3_2 16 62 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 62
  95 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 62 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 62 95 (Polychromatic418967fa.accept_13_1_10_4_1_954 14 62 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 62 95 (accept_3_2 13 62 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 62 95 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 62 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 62 95 (Polychromatic418967fa.accept_9_2_8_5_1_228 11
  62 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 62 95 (accept_3_2 10 62 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 62 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 62
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 62 95
  (Polychromatic418967fa.accept_10_8_2_5_1_596 8 62 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 62 95 (accept_3_2 7 62 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 62 95
  (Polychromatic418967fa.accept_9_6_8_5_1_837 6 62 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 62 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 62 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 95 (accept_3_2 4 62 95 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 62 95 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 62 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 95 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 62 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 95 (accept_3_2 1 62 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 62 95)))))))))))))))))))))))))))))))))) (allB_succ' 35 61 95 (Eq.refl
  Bool.true) (allA_of_3_0 35 61 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 60 95 (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 60 95 5 7 12 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 60 95 (accept_3_2 34 60 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 60
  95 (Polychromatic418967fa.accept_17_16_9_10_1_3962 33 60 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 60 95 (Polychromatic418967fa.accept_22_10_16_7_1_2608 32 60 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 95 (accept_3_2 31 60 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 95 5 6 12 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 60 95 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 60 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 60 95 (accept_3_2 28 60 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 60 95 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 60 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 60 95
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 60 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 60 95 5 5 12 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 60 95 (Polychromatic418967fa.accept_13_11_8_4_1_3950 24 60 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 60 95 (Polychromatic418967fa.accept_13_10_8_4_1_3098 23 60 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 60 95 (accept_3_2 22 60 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 60 95 (Polychromatic418967fa.accept_9_3_6_5_1_63 21
  60 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 60 95 5 4 12 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 95 (accept_3_2 19 60
  95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 95
  (Polychromatic418967fa.accept_16_2_12_15_1_2908 18 60 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 60 95 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 60 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 60 95 (accept_3_2 16 60 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 60 95 5 3 12 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 60 95 (Polychromatic418967fa.accept_21_14_18_11_1_3961 14 60 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 95 (accept_3_2 13 60 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 95 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 60 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 60 95
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 60 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 60 95 5 2 12 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 60 95 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 60 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 60 95 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 60 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 95 (accept_3_2 7 60 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 95 (Polychromatic418967fa.accept_21_6_18_11_1_3960 6 60 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 60 95 5 1 12 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 60 95 (accept_3_2 4 60 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 60 95 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 60 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 60 95
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 60 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 60 95 (accept_3_2 1 60 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  95)))))))))))))))))))))))))))))))))))) (allB_succ' 37 59 95 (Eq.refl Bool.true) (allA_succ_of_accept 36 59 95
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 59 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 59 95 (Polychromatic418967fa.accept_13_9_7_4_1_953 35 59 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 59 95 (accept_3_2 34 59 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 59 95 (Polychromatic418967fa.accept_16_1_11_15_1_498 33 59 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 59 95 (Polychromatic418967fa.accept_13_6_7_4_1_2264
  32 59 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 95 (accept_3_2 31 59
  95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 95
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 30 59 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 59 95 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 59 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 59 95 (accept_3_2 28 59 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 59 95 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 59 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 59 95 (Polychromatic418967fa.accept_10_6_9_5_1_1046
  26 59 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 95 (accept_3_2 25 59
  95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 95 (Polychromatic418967fa.accept_10_4_9_5_1_84
  24 59 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 95
  (Polychromatic418967fa.accept_13_10_7_4_1_2262 23 59 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 95 (accept_3_2 22 59 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 59
  95 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 59 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 59 95 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 59 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 95 (accept_3_2 19 59 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 59 95 (Polychromatic418967fa.accept_27_18_5_14_1_3959 18 59 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 95 (Polychromatic418967fa.accept_15_2_14_5_1_2072
  17 59 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 59 95 (accept_3_2 16 59
  95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 59 95 (Polychromatic418967fa.accept_7_1_3_4_1_128
  15 59 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 59 95
  (Polychromatic418967fa.accept_10_4_9_5_1_84 14 59 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 59 95 (accept_3_2 13 59 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 59
  95 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 59 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 59 95 (Polychromatic418967fa.accept_10_1_9_5_1_83 11 59 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 59 95 (accept_3_2 10 59 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 59 95 (Polychromatic418967fa.accept_13_9_7_4_1_953 9 59 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 59 95 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 59
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 95 (accept_3_2 7 59 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 95 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 59
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 95
  (Polychromatic418967fa.accept_20_5_19_15_1_3946 5 59 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 95 (accept_3_2 4 59 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59 95
  (Polychromatic418967fa.accept_11_3_4_7_1_114 3 59 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 95 (Polychromatic418967fa.accept_15_2_14_5_1_2072 2 59 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 95 (accept_3_2 1 59 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 95))))))))))))))))))))))))))))))))))))) (allB_succ' 38 58 95 (Eq.refl Bool.true) (allA_of_3_0
  38 58 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 57 95 (Eq.refl Bool.true) (allA_succ_of_gcd 38 57 95
  19 2 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 57 95
  (accept_3_2 37 57 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 57 95
  (Polychromatic418967fa.accept_13_10_5_4_1_3107 36 57 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 57 95 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 57 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 95 (accept_3_2 34 57 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 57 95 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 57 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 95 (Polychromatic418967fa.accept_6_2_3_5_1_26 32
  57 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 95 (accept_3_2 31 57 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 57 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 30
  57 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 95
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 57 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 57 95 (accept_3_2 28 57 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57
  95 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 57 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 57 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 57 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 95 (accept_3_2 25 57 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 57 95 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 57 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 95 (Polychromatic418967fa.accept_10_3_7_5_1_288 23
  57 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 95 (accept_3_2 22 57 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 95 (Polychromatic418967fa.accept_15_6_12_5_1_2108
  21 57 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 95
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 57 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 19 57 95 19 1 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 18 57 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 57 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 95 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 57 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 95 (accept_3_2 16 57 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 95 (Polychromatic418967fa.accept_9_6_3_5_1_240 15
  57 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 95
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 57 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 95 (accept_3_2 13 57 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 57
  95 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 57 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 57 95 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 57 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 95 (accept_3_2 10 57 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 57 95 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 57 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 95 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 57
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 95 (accept_3_2 7 57 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 57
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 57 95
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 57 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 57 95 (accept_3_2 4 57 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 57 95
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 57 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 57 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 57 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 95 (accept_3_2 1 57 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 57 95))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 56 95 (Eq.refl Bool.true)
  (allA_succ_of_accept 39 56 95 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 56 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 95 (Polychromatic418967fa.accept_12_2_8_11_1_31 38 56 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 56 95 (accept_3_2 37 56 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 56 95 (Polychromatic418967fa.accept_15_6_11_5_1_168
  36 56 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 56 95
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 56 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 56 95 (accept_3_2 34 56 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 56
  95 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 56 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 56 95 (Polychromatic418967fa.accept_15_2_11_5_1_1266 32 56 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 56 95 (accept_3_2 31 56 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 56 95 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 56 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 56 95 (Polychromatic418967fa.accept_10_9_6_5_1_1002
  29 56 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 95 (accept_3_2 28 56
  95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 56 95 (Polychromatic418967fa.accept_6_3_2_5_1_32
  27 56 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 95
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 56 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 56 95 (accept_3_2 25 56 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 56
  95 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 56 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 56 95 (Polychromatic418967fa.accept_15_8_11_5_1_169 23 56 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 95 (accept_3_2 22 56 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 56 95 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 56 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 95 (Polychromatic418967fa.accept_16_4_8_15_1_1113
  20 56 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 56 95 (accept_3_2 19 56
  95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 56 95
  (Polychromatic418967fa.accept_20_18_16_15_1_3958 18 56 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 56 95 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 56 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 95 (accept_3_2 16 56 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 56 95 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 56 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 95 (Polychromatic418967fa.accept_10_4_6_5_1_74 14
  56 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 56 95 (accept_3_2 13 56 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 56 95 (Polychromatic418967fa.accept_9_3_2_5_1_234 12
  56 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 56 95
  (Polychromatic418967fa.accept_10_1_6_5_1_304 11 56 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 56 95 (accept_3_2 10 56 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 56
  95 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 56 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 56 95 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 56 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 56 95 (accept_3_2 7 56 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 56 95 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 56 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 56 95 (Polychromatic418967fa.accept_20_5_16_15_1_3957
  5 56 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 95 (accept_3_2 4 56 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 56 95 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 56
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 95
  (Polychromatic418967fa.accept_12_2_8_11_1_31 2 56 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 56 95 (accept_3_2 1 56 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56
  95)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 55 95 (Eq.refl Bool.true) (allA_of_3_0 41 55 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 54 95 (Eq.refl Bool.true) (allA_succ_of_accept 41 54 95
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 54 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 54 95 (accept_3_2 40 54 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 54
  95 (Polychromatic418967fa.accept_10_9_4_5_1_616 39 54 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 54 95 (Polychromatic418967fa.accept_13_12_2_4_1_3131 38 54 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 95 (accept_3_2 37 54 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 54 95 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 54 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 54 95
  (Polychromatic418967fa.accept_21_14_12_11_1_3956 35 54 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 54 95 (accept_3_2 34 54 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 54
  95 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 54 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 54 95 (Polychromatic418967fa.accept_13_6_2_4_1_923 32 54 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 95 (accept_3_2 31 54 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 54 95 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 54 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 54 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 54
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 95 (accept_3_2 28 54 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 54 95 (Polychromatic418967fa.accept_7_6_5_4_1_297 27
  54 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 95
  (Polychromatic418967fa.accept_10_6_4_5_1_615 26 54 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 54 95 (accept_3_2 25 54 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54
  95 (Polychromatic418967fa.accept_13_11_2_4_1_1590 24 54 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 54 95 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 54 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 95 (accept_3_2 22 54 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 54 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 54 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 95
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 54 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 54 95 (accept_3_2 19 54 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 54
  95 (Polychromatic418967fa.accept_13_5_2_4_1_3955 18 54 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 54 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 54 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 95 (accept_3_2 16 54 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 54 95 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 54 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 95 (Polychromatic418967fa.accept_11_3_10_7_1_129
  14 54 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 95 (accept_3_2 13 54
  95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 54 95
  (Polychromatic418967fa.accept_13_12_2_4_1_3131 12 54 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 54 95 (Polychromatic418967fa.accept_10_1_4_5_1_1031 11 54 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 95 (accept_3_2 10 54 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 54 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 54 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 95 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 54
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 95 (accept_3_2 7 54 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54 95 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 54
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 54 95
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 54 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 54 95 (accept_3_2 4 54 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 54 95
  (Polychromatic418967fa.accept_11_3_10_7_1_129 3 54 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 54 95 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 54 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 95 (accept_3_2 1 54 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 54 95)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 53 95 (Eq.refl Bool.true)
  (allA_succ_of_accept 42 53 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 53 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 95 (Polychromatic418967fa.accept_15_11_8_5_1_1278 41 53 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 95 (accept_3_2 40 53 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 95 (Polychromatic418967fa.accept_9_3_8_5_1_65 39
  53 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 53 95
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 53 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 53 95 (accept_3_2 37 53 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 53
  95 (Polychromatic418967fa.accept_13_10_1_4_1_3103 36 53 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 53 95 (Polychromatic418967fa.accept_11_2_9_7_1_124 35 53 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 53 95 (accept_3_2 34 53 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 53 95 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 53 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 53 95
  (Polychromatic418967fa.accept_10_2_3_5_1_996 32 53 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 53 95 (accept_3_2 31 53 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 53
  95 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 53 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 53 95 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 53 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 95 (accept_3_2 28 53 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 53 95 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 53 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 53 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 26
  53 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 95 (accept_3_2 25 53 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 95 (Polychromatic418967fa.accept_9_6_8_5_1_837 24
  53 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 95
  (Polychromatic418967fa.accept_13_10_1_4_1_3103 23 53 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 95 (accept_3_2 22 53 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 53
  95 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 53 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 53 95 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 53 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 95 (accept_3_2 19 53 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 53 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 53 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 95 (Polychromatic418967fa.accept_10_7_3_5_1_301 17
  53 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 95 (accept_3_2 16 53 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 53 95 (Polychromatic418967fa.accept_9_6_8_5_1_837 15
  53 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 95
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 53 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 53 95 (accept_3_2 13 53 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 53
  95 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 53 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 53 95 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 53 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 95 (accept_3_2 10 53 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 53 95 (Polychromatic418967fa.accept_27_9_26_14_1_3954 9 53 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 95 (Polychromatic418967fa.accept_10_8_3_5_1_613 8
  53 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 95 (accept_3_2 7 53 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 53
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 95
  (Polychromatic418967fa.accept_11_5_9_7_1_411 5 53 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 95 (accept_3_2 4 53 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53 95
  (Polychromatic418967fa.accept_9_3_8_5_1_65 3 53 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 53 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 95 (accept_3_2 1 53 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 95))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 52 95 (Eq.refl Bool.true)
  (allA_of_3_0 44 52 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 51 95 (Eq.refl Bool.true)
  (allA_succ_of_accept 44 51 95 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 51 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 95 (accept_3_2 43 51 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 51 95 (Polychromatic418967fa.accept_13_3_12_4_1_110 42 51 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 95 (Polychromatic418967fa.accept_7_6_2_4_1_291 41
  51 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 95 (accept_3_2 40 51 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 95 (Polychromatic418967fa.accept_9_3_6_5_1_63 39
  51 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 95
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 51 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 95 (accept_3_2 37 51 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 51
  95 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 51 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 51 95 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 51 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 95 (accept_3_2 34 51 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 51 95 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 51 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 95 (Polychromatic418967fa.accept_6_2_3_5_1_26 32
  51 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 95 (accept_3_2 31 51 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 51 95 (Polychromatic418967fa.accept_9_3_6_5_1_63 30
  51 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 95
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 51 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 51 95 (accept_3_2 28 51 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51
  95 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 51 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 51 95 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 51 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 95 (accept_3_2 25 51 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 51 95 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 51 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 95 (Polychromatic418967fa.accept_16_7_3_15_1_2940
  23 51 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 95 (accept_3_2 22 51
  95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 95 (Polychromatic418967fa.accept_9_3_6_5_1_63
  21 51 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 95
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 51 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 95 (accept_3_2 19 51 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 51
  95 (Polychromatic418967fa.accept_13_5_12_4_1_449 18 51 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 51 95 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 51 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 95 (accept_3_2 16 51 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 51 95 (Polychromatic418967fa.accept_13_2_12_4_1_943 15 51 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 95 (Polychromatic418967fa.accept_6_2_3_5_1_26 14
  51 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 95 (accept_3_2 13 51 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 95 (Polychromatic418967fa.accept_7_5_2_4_1_126 12
  51 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 95
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 51 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 51 95 (accept_3_2 10 51 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51
  95 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 51 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 51 95 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 51 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 95 (accept_3_2 7 51 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 51 95 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 51 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 95 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 51
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 95 (accept_3_2 4 51 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51 95 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 51
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 95
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 51 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 51 95 (accept_3_2 1 51 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  95))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 50 95 (Eq.refl Bool.true) (allA_succ_of_gcd 45 50 95 5
  9 10 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 50 95
  (Polychromatic418967fa.accept_12_8_2_11_1_246 44 50 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 50 95 (accept_3_2 43 50 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 50
  95 (Polychromatic418967fa.accept_20_2_10_15_1_3953 42 50 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 50 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 50 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 50 95 5 8 10 19 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 50 95 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 50
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 95
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 50 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 50 95 (accept_3_2 37 50 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 50
  95 (Polychromatic418967fa.accept_13_10_11_4_1_2248 36 50 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 50 95 5 7 10 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 50 95 (accept_3_2 34 50 95 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 50 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 50 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 95 (Polychromatic418967fa.accept_12_8_2_11_1_246 32 50 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 50 95 (accept_3_2 31 50 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50 95 5 6 10 19 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 50 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 50
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 95 (accept_3_2 28 50 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 95 (Polychromatic418967fa.accept_6_3_2_5_1_32 27
  50 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 95
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 50 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 50 95 5 5 10 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 50 95 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 50 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 50 95 (Polychromatic418967fa.accept_11_1_6_7_1_116 23 50 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 95 (accept_3_2 22 50 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 50
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 95 5 4 10 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 95 (accept_3_2 19 50
  95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 50 95
  (Polychromatic418967fa.accept_14_4_8_11_1_794 18 50 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 50 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 50 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 95 (accept_3_2 16 50 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 50 95 5 3 10 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 50 95 (Polychromatic418967fa.accept_20_14_10_15_1_3952 14 50 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 50 95 (accept_3_2 13 50 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 50 95 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 50 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 50 95
  (Polychromatic418967fa.accept_18_11_14_5_1_3951 11 50 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 50 95 5 2 10 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 50 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 50 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 95 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 50 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 50 95 (accept_3_2 7 50 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50 95 (Polychromatic418967fa.accept_13_6_11_4_1_938 6 50 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 50 95 5 1 10 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 50 95 (accept_3_2 4 50 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 50 95 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 50 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 95
  (Polychromatic418967fa.accept_13_2_11_4_1_445 2 50 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 50 95 (accept_3_2 1 50 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50
  95)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 49 95 (Eq.refl Bool.true) (allA_of_3_0 47 49 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 95 (allA_succ_of_accept 47 48 95
  (Polychromatic418967fa.accept_7_5_6_4_1_117 47 48 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 48 95 (accept_3_2 46 48 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 48
  95 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 48 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 48 95 (Polychromatic418967fa.accept_7_2_6_4_1_29 44 48 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 95 (accept_3_2 43 48 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 48 95 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 48 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 48 95 (Polychromatic418967fa.accept_11_8_4_7_1_1303
  41 48 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 95 (accept_3_2 40 48
  95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 48 95
  (Polychromatic418967fa.accept_15_9_3_5_1_2077 39 48 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 48 95 (Polychromatic418967fa.accept_7_3_6_4_1_30 38 48 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 95 (accept_3_2 37 48 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 48 95 (Polychromatic418967fa.accept_11_3_4_7_1_114 36 48 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 48 95 (Polychromatic418967fa.accept_9_8_3_5_1_241 35
  48 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 48 95 (accept_3_2 34 48 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 48 95 (Polychromatic418967fa.accept_7_5_6_4_1_117 33
  48 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 48 95
  (Polychromatic418967fa.accept_10_2_8_5_1_587 32 48 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 48 95 (accept_3_2 31 48 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 48
  95 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 48 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 48 95 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 48 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 48 95 (accept_3_2 28 48 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 48 95 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 48 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 48 95 (Polychromatic418967fa.accept_7_5_6_4_1_117 26
  48 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 95 (accept_3_2 25 48 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 95 (Polychromatic418967fa.accept_7_3_6_4_1_30 24
  48 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 48 95
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 48 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 48 95 (accept_3_2 22 48 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 48
  95 (Polychromatic418967fa.accept_13_8_9_4_1_1552 21 48 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 48 95 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 48 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 95 (accept_3_2 19 48 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 48 95 (Polychromatic418967fa.accept_13_5_9_4_1_441 18 48 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 48 95 (Polychromatic418967fa.accept_7_3_6_4_1_30 17
  48 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 48 95 (accept_3_2 16 48 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 48 95 (Polychromatic418967fa.accept_9_6_3_5_1_240 15
  48 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 48 95
  (Polychromatic418967fa.accept_11_3_4_7_1_114 14 48 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 48 95 (accept_3_2 13 48 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 48
  95 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 48 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 48 95 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 48 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 48 95 (accept_3_2 10 48 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 48 95 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 48 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 48 95 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 48
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 95 (accept_3_2 7 48 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 95 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 48
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 48 95
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 48 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 48 95 (accept_3_2 4 48 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 48 95
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 48 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 48 95 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 48 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 95 (accept_3_2 1 48 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 48 95)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 95 (allA_succ_of_accept 46
  47 95 (accept_3_2 46 47 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 95
  (Polychromatic418967fa.accept_20_5_7_15_1_2668 45 47 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 95 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 47 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 95 (accept_3_2 43 47 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 95 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 47 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 95 (Polychromatic418967fa.accept_7_6_5_4_1_297 41
  47 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 95 (accept_3_2 40 47 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 95 (Polychromatic418967fa.accept_9_3_2_5_1_234 39
  47 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 47 95
  (Polychromatic418967fa.accept_10_8_7_5_1_602 38 47 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 47 95 (accept_3_2 37 47 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 47
  95 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 47 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 47 95 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 47 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 95 (accept_3_2 34 47 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 47 95 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 47 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 47 95 (Polychromatic418967fa.accept_10_2_7_5_1_605 32
  47 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 95 (accept_3_2 31 47 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 95 (Polychromatic418967fa.accept_7_2_5_4_1_115 30
  47 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 95
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 47 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 95 (accept_3_2 28 47 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 47
  95 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 47 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 47 95 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 47 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 95 (accept_3_2 25 47 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 47 95 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 47 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 95 (Polychromatic418967fa.accept_7_2_5_4_1_115 23
  47 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 95 (accept_3_2 22 47 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 95 (Polychromatic418967fa.accept_9_3_2_5_1_234 21
  47 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 47 95
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 47 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 47 95 (accept_3_2 19 47 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 47
  95 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 47 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 47 95 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 47 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 95 (accept_3_2 16 47 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 47 95 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 47 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 95 (Polychromatic418967fa.accept_15_14_2_5_1_1272
  14 47 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 95 (accept_3_2 13 47
  95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 95 (Polychromatic418967fa.accept_9_3_2_5_1_234
  12 47 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 95
  (Polychromatic418967fa.accept_13_11_8_4_1_3950 11 47 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 95 (accept_3_2 10 47 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 47
  95 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 47 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 47 95 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 47 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 95 (accept_3_2 7 47 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 47 95 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 47 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 95 (Polychromatic418967fa.accept_17_5_13_10_1_3949
  5 47 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 95 (accept_3_2 4 47 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47 95 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 47
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 95
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 47 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 47 95 (accept_3_2 1 47 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47
  95))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 95 (allA_of_3_0 46 46 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 45 95 (allA_succ_of_accept 44 45 95 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 45 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 95 (accept_3_2 43 45 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 45 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 42
  45 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 95
  (Polychromatic418967fa.accept_7_6_3_4_1_294 41 45 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 45 95 5 8 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 45 95 (Polychromatic418967fa.accept_11_6_1_7_1_1315 39 45 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 45 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 95 (accept_3_2 37 45 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 95 (Polychromatic418967fa.accept_7_1_3_4_1_128 36
  45 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 45 95 5 7 9 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 45 95 (accept_3_2 34 45
  95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 95 (Polychromatic418967fa.accept_13_7_6_4_1_933
  33 45 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 95
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 45 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 95 (accept_3_2 31 45 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45 95
  5 6 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 95
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 45 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 45 95 (accept_3_2 28 45 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 45
  95 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 45 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 45 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 45 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 45 95 5 5 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 45 95 (Polychromatic418967fa.accept_13_11_6_4_1_3121 24 45 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 95
  (Polychromatic418967fa.accept_13_10_6_4_1_1583 23 45 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 45 95 (accept_3_2 22 45 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45
  95 (Polychromatic418967fa.accept_14_7_3_11_1_2199 21 45 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 45 95 5 4 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 45 95 (accept_3_2 19 45 95 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 45 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 45 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 95 (Polychromatic418967fa.accept_11_6_1_7_1_1315 17 45 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 95 (accept_3_2 16 45 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 95 5 3 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 45
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 95 (accept_3_2 13 45 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 95
  (Polychromatic418967fa.accept_16_12_13_15_1_1966 12 45 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 45 95 (Polychromatic418967fa.accept_13_11_6_4_1_3121 11 45 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 45 95 5 2 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 45 95 (Polychromatic418967fa.accept_13_9_6_4_1_2243 9 45 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 95
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 45 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 95 (accept_3_2 7 45 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 95
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 45 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 45 95 5 1 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 45 95 (accept_3_2 4 45 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 95
  (Polychromatic418967fa.accept_12_3_9_11_1_231 3 45 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 45 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 45 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 95 (accept_3_2 1 45 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 45 95))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 95 (allA_succ_of_accept 43 44
  95 (accept_3_2 43 44 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 44 95
  (Polychromatic418967fa.accept_9_6_8_5_1_837 42 44 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 44 95 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 44 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 95 (accept_3_2 40 44 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 44 95 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 44 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 95 (Polychromatic418967fa.accept_9_2_8_5_1_228 38
  44 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 44 95 (accept_3_2 37 44 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 44 95 (Polychromatic418967fa.accept_10_6_4_5_1_615 36
  44 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 44 95
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 44 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 44 95 (accept_3_2 34 44 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 44
  95 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 44 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 44 95 (Polychromatic418967fa.accept_13_6_5_4_1_3924 32 44 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 44 95 (accept_3_2 31 44 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 44 95 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 44 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 44 95 (Polychromatic418967fa.accept_9_2_8_5_1_228 29
  44 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 95 (accept_3_2 28 44 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 44 95 (Polychromatic418967fa.accept_6_3_2_5_1_32 27
  44 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 95
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 44 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 44 95 (accept_3_2 25 44 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 44
  95 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 44 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 44 95 (Polychromatic418967fa.accept_13_10_5_4_1_3107 23 44 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 95 (accept_3_2 22 44 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 44 95 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 44 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 95 (Polychromatic418967fa.accept_7_6_2_4_1_291 20
  44 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 44 95 (accept_3_2 19 44 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 44 95 (Polychromatic418967fa.accept_16_2_12_15_1_2908
  18 44 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 44 95
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 17 44 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 44 95 (accept_3_2 16 44 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 44
  95 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 44 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 44 95 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 44 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 44 95 (accept_3_2 13 44 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 44 95 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 44 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 44 95 (Polychromatic418967fa.accept_8_3_4_7_1_475 11
  44 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 95 (accept_3_2 10 44 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 44 95 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 44
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 95
  (Polychromatic418967fa.accept_15_8_14_5_1_2089 8 44 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 44 95 (accept_3_2 7 44 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44 95
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 44 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 44 95 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 44 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 44 95 (accept_3_2 4 44 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 44 95 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 44 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 44 95 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 44
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 95 (accept_3_2 1 44 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 95)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 95
  (allA_of_3_0 43 43 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 95 (allA_succ_of_accept 41 42 95
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 42 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 95 (accept_3_2 40 42 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 42
  95 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 42 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 42 95 (Polychromatic418967fa.accept_9_2_6_5_1_227 38 42 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 95 (accept_3_2 37 42 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 42 95 (Polychromatic418967fa.accept_15_6_12_5_1_2108 36 42 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 42 95 (Polychromatic418967fa.accept_9_8_6_5_1_513 35
  42 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 42 95 (accept_3_2 34 42 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 42 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 42
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 42 95
  (Polychromatic418967fa.accept_15_2_12_5_1_2107 32 42 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 42 95 (accept_3_2 31 42 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 42
  95 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 42 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 42 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 42 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 42 95 (accept_3_2 28 42 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 42 95 (Polychromatic418967fa.accept_10_7_2_5_1_298 27 42 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 42 95 (Polychromatic418967fa.accept_9_8_6_5_1_513 26
  42 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 95 (accept_3_2 25 42 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 95 (Polychromatic418967fa.accept_11_2_9_7_1_124 24
  42 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 42 95
  (Polychromatic418967fa.accept_10_3_2_5_1_295 23 42 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 42 95 (accept_3_2 22 42 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 42
  95 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 42 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 42 95 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 42 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 95 (accept_3_2 19 42 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 42 95 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 42 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 42 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 42
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 42 95 (accept_3_2 16 42 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 42 95 (Polychromatic418967fa.accept_17_15_8_10_1_2886
  15 42 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 42 95
  (Polychromatic418967fa.accept_13_1_3_4_1_925 14 42 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 42 95 (accept_3_2 13 42 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 42
  95 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 42 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 42 95 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 42 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 42 95 (accept_3_2 10 42 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 42 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 42 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 42 95 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 42
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 95 (accept_3_2 7 42 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 42 95 (Polychromatic418967fa.accept_15_6_12_5_1_2108 6
  42 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 42 95
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 42 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 42 95 (accept_3_2 4 42 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 42 95
  (Polychromatic418967fa.accept_9_3_6_5_1_63 3 42 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 42 95 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 42 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 95 (accept_3_2 1 42 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 42 95)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 95 (allA_succ_of_accept 40 41 95
  (accept_3_2 40 41 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 95
  (Polychromatic418967fa.accept_10_9_1_5_1_594 39 41 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 41 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 95 (accept_3_2 37 41 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 95 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 41 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 95 (Polychromatic418967fa.accept_17_1_7_10_1_1835
  35 41 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 95 (accept_3_2 34 41
  95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 95 (Polychromatic418967fa.accept_7_5_6_4_1_117
  33 41 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 95
  (Polychromatic418967fa.accept_13_6_2_4_1_923 32 41 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 95 (accept_3_2 31 41 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 41
  95 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 41 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 41 95 (Polychromatic418967fa.accept_10_9_1_5_1_594 29 41 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 95 (accept_3_2 28 41 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 41 95 (Polychromatic418967fa.accept_20_7_1_15_1_2700 27 41 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 26
  41 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 95 (accept_3_2 25 41 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 95 (Polychromatic418967fa.accept_7_3_6_4_1_30 24
  41 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 95
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 41 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 95 (accept_3_2 22 41 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 41
  95 (Polychromatic418967fa.accept_15_6_11_5_1_168 21 41 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 41 95 (Polychromatic418967fa.accept_17_3_7_10_1_3948 20 41 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 95 (accept_3_2 19 41 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 41 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 41 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 95 (Polychromatic418967fa.accept_7_3_6_4_1_30 17
  41 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 95 (accept_3_2 16 41 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 95 (Polychromatic418967fa.accept_11_4_8_7_1_819 15
  41 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 95
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 41 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 95 (accept_3_2 13 41 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 41
  95 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 41 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 41 95 (Polychromatic418967fa.accept_13_11_2_4_1_1590 11 41 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 95 (accept_3_2 10 41 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 41 95 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 41 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 95 (Polychromatic418967fa.accept_15_8_11_5_1_169 8
  41 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 95 (accept_3_2 7 41 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 41
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 95
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 41 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 95 (accept_3_2 4 41 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41 95
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 41 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 41 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 95 (accept_3_2 1 41 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 95))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 95 (allA_of_3_0 40 40 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 39 95 (allA_succ_of_accept 38 39 95
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 39 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 95 (accept_3_2 37 39 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 39
  95 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 39 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 39 95 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 39 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 95 (accept_3_2 34 39 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 39 95 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 39 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 95 (Polychromatic418967fa.accept_6_2_3_5_1_26 32
  39 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 95 (accept_3_2 31 39 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 39 95 (Polychromatic418967fa.accept_16_14_7_15_1_3947
  30 39 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 39 95
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 39 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 95 (accept_3_2 28 39 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 39
  95 (Polychromatic418967fa.accept_15_12_9_5_1_2973 27 39 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 39 95 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 39 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 95 (accept_3_2 25 39 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 39 95 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 39 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 95
  (Polychromatic418967fa.accept_11_1_6_7_1_116 23 39 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 39 95 (accept_3_2 22 39 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39
  95 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 39 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 39 95 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 39 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 95 (accept_3_2 19 39 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 39 95 (Polychromatic418967fa.accept_15_3_9_5_1_2082 18 39 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 39 95 (Polychromatic418967fa.accept_9_8_3_5_1_241 17
  39 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 95 (accept_3_2 16 39 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 95 (Polychromatic418967fa.accept_9_6_3_5_1_240 15
  39 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 95
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 39 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 95 (accept_3_2 13 39 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 39
  95 (Polychromatic418967fa.accept_11_1_6_7_1_116 12 39 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 39 95 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 39 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 95 (accept_3_2 10 39 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 39 95 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 39 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 95 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 39
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 95 (accept_3_2 7 39 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 95 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 39
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 39 95
  (Polychromatic418967fa.accept_20_5_19_15_1_3946 5 39 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 39 95 (accept_3_2 4 39 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 39 95
  (Polychromatic418967fa.accept_15_3_9_5_1_2082 3 39 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 39 95 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 39 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 95 (accept_3_2 1 39 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 39 95))))))))))))))))))))))))))))))))))))))) (allB_succ 38 95 (allA_succ_of_accept 37 38 95
  (accept_3_2 37 38 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 38 95
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 38 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 38 95 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 38 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 95 (accept_3_2 34 38 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 38 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 38 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 95 (Polychromatic418967fa.accept_10_2_8_5_1_587 32
  38 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 38 95 (accept_3_2 31 38 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 38 95 (Polychromatic418967fa.accept_9_3_2_5_1_234 30
  38 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 38 95
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 38 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 38 95 (accept_3_2 28 38 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 38
  95 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 38 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 38 95 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 38 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 38 95 (accept_3_2 25 38 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 38 95 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 38 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 38 95 (Polychromatic418967fa.accept_10_3_8_5_1_606 23
  38 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 95 (accept_3_2 22 38 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 38
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 95
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 38 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 19 38 95 19 1 2 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 18 38 95 (Polychromatic418967fa.accept_13_5_12_4_1_449 18 38 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 38 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 38 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 95 (accept_3_2 16 38 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 95 (Polychromatic418967fa.accept_6_3_2_5_1_32 15
  38 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 95
  (Polychromatic418967fa.accept_15_14_8_5_1_2104 14 38 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 95 (accept_3_2 13 38 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 38
  95 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 38 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 38 95 (Polychromatic418967fa.accept_13_11_12_4_1_3945 11 38 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 95 (accept_3_2 10 38 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 38 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 38 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 95 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 38
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 38 95 (accept_3_2 7 38 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38 95 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 38
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 38 95
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 38 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 38 95 (accept_3_2 4 38 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 38 95
  (Polychromatic418967fa.accept_6_3_2_5_1_32 3 38 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 38 95 (Polychromatic418967fa.accept_10_2_8_5_1_587 2 38 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 95 (accept_3_2 1 38 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 38 95)))))))))))))))))))))))))))))))))))))) (allB_succ 37 95 (allA_of_3_0 37 37 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 36 95 (allA_succ_of_accept 35 36 95
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 36 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 95 (accept_3_2 34 36 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 36
  95 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 36 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 36 95 (Polychromatic418967fa.accept_11_10_3_7_1_2564 32 36 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 95 (accept_3_2 31 36 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 36 95 (Polychromatic418967fa.accept_16_14_4_15_1_3944 30 36 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 36 95 (Polychromatic418967fa.accept_10_9_6_5_1_1002
  29 36 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 95 (accept_3_2 28 36
  95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 36 95 (Polychromatic418967fa.accept_8_3_4_7_1_475
  27 36 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 36 95
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 36 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 36 95 (accept_3_2 25 36 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 36
  95 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 36 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 36 95 (Polychromatic418967fa.accept_25_23_11_20_1_3943 23 36 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 36 95 (accept_3_2 22 36 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 36 95 (Polychromatic418967fa.accept_10_1_6_5_1_304 21 36 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 36 95 (Polychromatic418967fa.accept_13_7_10_4_1_919
  20 36 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 95 (accept_3_2 19 36
  95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 95
  (Polychromatic418967fa.accept_13_5_10_4_1_1564 18 36 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 36 95 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 36 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 36 95 (accept_3_2 16 36 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 36 95 (Polychromatic418967fa.accept_11_4_3_7_1_828 15 36 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 36 95 (Polychromatic418967fa.accept_10_4_6_5_1_74 14
  36 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 95 (accept_3_2 13 36 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 95 (Polychromatic418967fa.accept_7_5_1_4_1_122 12
  36 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 36 95
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 36 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 36 95 (accept_3_2 10 36 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 36
  95 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 36 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 36 95 (Polychromatic418967fa.accept_13_8_10_4_1_2270 8 36 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 95 (accept_3_2 7 36 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 36 95 (Polychromatic418967fa.accept_13_6_10_4_1_957 6 36 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 36 95 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 36
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36 95 (accept_3_2 4 36 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 36 95 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 36
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 36 95
  (Polychromatic418967fa.accept_23_2_13_3_1_3942 2 36 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 36 95 (accept_3_2 1 36 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36
  95)))))))))))))))))))))))))))))))))))) (allB_succ 35 95 (allA_succ_of_accept 34 35 95 (accept_3_2 34 35 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 95 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 35 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 35 95
  (Polychromatic418967fa.accept_13_6_9_4_1_2288 32 35 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 35 95 (accept_3_2 31 35 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 35 95
  5 6 7 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 35 95
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 35 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 35 95 (accept_3_2 28 35 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35
  95 (Polychromatic418967fa.accept_16_11_3_15_1_1989 27 35 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 35 95 (Polychromatic418967fa.accept_17_9_1_10_1_2859 26 35 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 35 95 5 5 7 19 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 35 95 (Polychromatic418967fa.accept_9_6_8_5_1_837 24
  35 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 95
  (Polychromatic418967fa.accept_16_7_3_15_1_2940 23 35 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 95 (accept_3_2 22 35 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35
  95 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 35 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 35 95 5 4 7 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 35 95 (accept_3_2 19 35 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 35
  95 (Polychromatic418967fa.accept_13_5_9_4_1_441 18 35 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 35 95 (Polychromatic418967fa.accept_14_3_7_11_1_765 17 35 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 95 (accept_3_2 16 35 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 35 95 5 3 7 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 35 95 (Polychromatic418967fa.accept_17_14_1_10_1_3941 14 35 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 95 (accept_3_2 13 35 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 95 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 35 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 95
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 35 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 35 95 5 2 7 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 35 95 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 35 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 95 (Polychromatic418967fa.accept_13_8_9_4_1_1552 8 35 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 95 (accept_3_2 7 35 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 95 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 35 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 35 95 5 1 7 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 35 95 (accept_3_2 4 35 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 95 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 35 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 95
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 35 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 95 (accept_3_2 1 35 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  95))))))))))))))))))))))))))))))))))) (allB_succ 34 95 (allA_of_3_0 34 34 95 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 33 95 (allA_succ_of_accept 32 33 95 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 33 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 95 (accept_3_2 31 33 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 33 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 95
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 33 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 33 95 (accept_3_2 28 33 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 33
  95 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 33 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 33 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 33 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 95 (accept_3_2 25 33 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 33 95 (Polychromatic418967fa.accept_13_11_7_4_1_1561 24 33 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 95 (Polychromatic418967fa.accept_7_2_5_4_1_115 23
  33 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 95 (accept_3_2 22 33 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 95 (Polychromatic418967fa.accept_9_3_6_5_1_63 21
  33 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 95
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 33 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 95 (accept_3_2 19 33 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 33
  95 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 33 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 33 95 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 33 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 95 (accept_3_2 16 33 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 33 95 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 33 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 14
  33 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 95 (accept_3_2 13 33 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 95 (Polychromatic418967fa.accept_9_3_6_5_1_63 12
  33 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 95
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 33 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 33 95 (accept_3_2 10 33 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33
  95 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 33 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 33 95 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 33 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 95 (accept_3_2 7 33 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 33 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 33 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 95 (Polychromatic418967fa.accept_16_5_1_15_1_3922 5
  33 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 95 (accept_3_2 4 33 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 95 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 33
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 95
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 33 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 33 95 (accept_3_2 1 33 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33
  95))))))))))))))))))))))))))))))))) (allB_succ 32 95 (allA_succ_of_accept 31 32 95 (accept_3_2 31 32 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 32 95 (Polychromatic418967fa.accept_20_10_12_15_1_3940 30 32
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 32 95
  (Polychromatic418967fa.accept_14_1_4_11_1_3036 29 32 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 32 95 (accept_3_2 28 32 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 32
  95 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 32 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 32 95 (Polychromatic418967fa.accept_12_2_8_11_1_31 26 32 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 32 95 (accept_3_2 25 32 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 32 95 (Polychromatic418967fa.accept_13_11_6_4_1_3121 24 32 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 32 95 (Polychromatic418967fa.accept_10_3_2_5_1_295 23
  32 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 95 (accept_3_2 22 32 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 32 95 (Polychromatic418967fa.accept_6_3_2_5_1_32 21
  32 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 95
  (Polychromatic418967fa.accept_13_7_6_4_1_933 20 32 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 32 95 (accept_3_2 19 32 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 32
  95 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 32 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 32 95 (Polychromatic418967fa.accept_10_7_2_5_1_298 17 32 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 95 (accept_3_2 16 32 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 32 95 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 32 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 95 (Polychromatic418967fa.accept_11_3_10_7_1_129
  14 32 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 32 95 (accept_3_2 13 32
  95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 32 95
  (Polychromatic418967fa.accept_15_12_2_5_1_3939 12 32 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 32 95 (Polychromatic418967fa.accept_13_11_6_4_1_3121 11 32 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 95 (accept_3_2 10 32 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 32 95 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 32 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 95 (Polychromatic418967fa.accept_10_8_2_5_1_596 8
  32 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 32 95 (accept_3_2 7 32 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32 95 (Polychromatic418967fa.accept_20_6_12_15_1_3938
  6 32 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 32 95
  (Polychromatic418967fa.accept_13_5_6_4_1_1582 5 32 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 32 95 (accept_3_2 4 32 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 32 95
  (Polychromatic418967fa.accept_6_3_2_5_1_32 3 32 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 32 95 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 32 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 95 (accept_3_2 1 32 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 95)))))))))))))))))))))))))))))))) (allB_succ 31 95 (allA_of_3_0 31 31 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 30 95 (allA_succ_of_accept 29 30 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 30 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 30 95 (accept_3_2 28 30 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 30 95 (Polychromatic418967fa.accept_7_6_2_4_1_291 27
  30 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 30 95
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 30 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 30 95 5 5 6 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 30 95 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 30 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 95 (Polychromatic418967fa.accept_14_9_2_11_1_780 23 30 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 95 (accept_3_2 22 30 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 30 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 30
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 30 95 5 4 6 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 95 (accept_3_2 19 30
  95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 95
  (Polychromatic418967fa.accept_20_18_10_15_1_3937 18 30 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 30 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 30 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 30 95 (accept_3_2 16 30 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 30 95 5 3 6 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 30 95 (Polychromatic418967fa.accept_17_14_13_10_1_3936 14 30 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 95 (accept_3_2 13 30 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 95 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 30 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 30 95
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 30 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 30 95 5 2 6 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 30 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 30 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 8 30 95 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 30 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 95 (accept_3_2 7 30 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 30 95 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 30 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 30 95 5 1 6 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 30 95 (accept_3_2 4 30 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30 95 (Polychromatic418967fa.accept_17_3_13_10_1_3935 3 30 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 95
  (Polychromatic418967fa.accept_9_2_3_5_1_60 2 30 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 30 95 (accept_3_2 1 30 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30
  95)))))))))))))))))))))))))))))) (allB_succ 29 95 (allA_succ_of_accept 28 29 95 (accept_3_2 28 29 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 95 (Polychromatic418967fa.accept_13_1_3_4_1_925 27 29 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 95
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 29 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 29 95 (accept_3_2 25 29 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 29
  95 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 29 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 29 95 (Polychromatic418967fa.accept_15_8_14_5_1_2089 23 29 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 95 (accept_3_2 22 29 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 29 95 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 29 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 95 (Polychromatic418967fa.accept_13_7_3_4_1_459 20
  29 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 95 (accept_3_2 19 29 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 18
  29 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 95
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 29 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 95 (accept_3_2 16 29 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 29
  95 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 29 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 29 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 29 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 95 (accept_3_2 13 29 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 29 95 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 29 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 95 (Polychromatic418967fa.accept_10_1_9_5_1_83 11
  29 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 95 (accept_3_2 10 29 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 95 (Polychromatic418967fa.accept_15_9_14_5_1_2086 9
  29 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 95
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 29 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 29 95 (accept_3_2 7 29 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 95
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 29 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 29 95 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 29 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 95 (accept_3_2 4 29 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 29 95 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 29 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 29
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 95 (accept_3_2 1 29 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29 95))))))))))))))))))))))))))))) (allB_succ 28 95 (allA_of_3_0 28
  28 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 27 95 (allA_succ_of_accept 26 27 95
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 27 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 95 (accept_3_2 25 27 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27
  95 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 27 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 27 95 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 27 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 95 (accept_3_2 22 27 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 27 95 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 27 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 95 (Polychromatic418967fa.accept_6_2_3_5_1_26 20
  27 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 95 (accept_3_2 19 27 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 95 (Polychromatic418967fa.accept_10_8_7_5_1_602 18
  27 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 95
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 27 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 27 95 (accept_3_2 16 27 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27
  95 (Polychromatic418967fa.accept_18_15_9_5_1_3934 15 27 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 27 95 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 27 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 95 (accept_3_2 13 27 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 95 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 27 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 95
  (Polychromatic418967fa.accept_22_11_5_7_1_3933 11 27 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 27 95 (accept_3_2 10 27 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27
  95 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 27 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 27 95 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 27 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 95 (accept_3_2 7 27 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 27 95 (Polychromatic418967fa.accept_15_6_12_5_1_2108 6 27 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 95 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 27
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 95 (accept_3_2 4 27 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 95 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 27
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 95
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 27 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 27 95 (accept_3_2 1 27 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27
  95))))))))))))))))))))))))))) (allB_succ 26 95 (allA_succ_of_accept 25 26 95 (accept_3_2 25 26 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 95 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 26 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 26 95
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 26 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 26 95 (accept_3_2 22 26 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 26
  95 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 26 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 26 95 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 26 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 95 (accept_3_2 19 26 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 26 95 (Polychromatic418967fa.accept_17_1_9_10_1_1864 18 26 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 26 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 26
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 95 (accept_3_2 16 26 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 26 95 (Polychromatic418967fa.accept_6_3_2_5_1_32 15
  26 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 95
  (Polychromatic418967fa.accept_10_4_6_5_1_74 14 26 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 26 95 (accept_3_2 13 26 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 26
  95 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 26 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 26 95 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 26 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 26 95 (accept_3_2 10 26 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 26 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 26 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 95 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 26
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 26 95 (accept_3_2 7 26 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26 95 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 26
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 26 95
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 26 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 26 95 (accept_3_2 4 26 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 26 95
  (Polychromatic418967fa.accept_6_3_2_5_1_32 3 26 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 26 95 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 26 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 95 (accept_3_2 1 26 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 26 95)))))))))))))))))))))))))) (allB_succ 25 95 (allA_of_3_0 25 25 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 24 95 (allA_succ_of_accept 23 24 95 (Polychromatic418967fa.accept_13_10_11_4_1_2248 23
  24 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 95 (accept_3_2 22 24 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 24 95 (Polychromatic418967fa.accept_9_3_6_5_1_63 21
  24 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 24 95
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 24 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 24 95 (accept_3_2 19 24 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 24
  95 (Polychromatic418967fa.accept_15_3_9_5_1_2082 18 24 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 24 95 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 24 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 95 (accept_3_2 16 24 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 24 95 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 24 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 24 95 (Polychromatic418967fa.accept_15_14_9_5_1_3932
  14 24 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 95 (accept_3_2 13 24
  95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 24 95 (Polychromatic418967fa.accept_9_3_6_5_1_63
  12 24 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 24 95
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 24 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 24 95 (accept_3_2 10 24 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 24
  95 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 24 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 24 95 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 24 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 95 (accept_3_2 7 24 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 24 95 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 24 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 24 95 (Polychromatic418967fa.accept_20_5_4_15_1_3931 5
  24 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 95 (accept_3_2 4 24 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 24 95 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 24
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 95
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 24 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 24 95 (accept_3_2 1 24 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24
  95)))))))))))))))))))))))) (allB_succ 23 95 (allA_succ_of_accept 22 23 95 (accept_3_2 22 23 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 95 (Polychromatic418967fa.accept_13_8_10_4_1_2270 21 23 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 23 95
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 23 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 23 95 (accept_3_2 19 23 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 23
  95 (Polychromatic418967fa.accept_10_8_3_5_1_613 18 23 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 23 95 (Polychromatic418967fa.accept_10_7_3_5_1_301 17 23 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 95 (accept_3_2 16 23 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 23 95 (Polychromatic418967fa.accept_25_15_23_20_1_3930 15 23 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 95
  (Polychromatic418967fa.accept_13_1_10_4_1_954 14 23 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 95 (accept_3_2 13 23 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 23
  95 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 23 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 23 95 (Polychromatic418967fa.accept_13_11_10_4_1_1565 11 23 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 95 (accept_3_2 10 23 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 23 95 (Polychromatic418967fa.accept_20_9_3_15_1_3929 9 23 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 95 (Polychromatic418967fa.accept_10_8_3_5_1_613 8
  23 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 95 (accept_3_2 7 23 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 95 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 23
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 95
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 23 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 95 (accept_3_2 4 23 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23 95
  (Polychromatic418967fa.accept_15_3_8_5_1_2105 3 23 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 23 95 (Polychromatic418967fa.accept_10_2_3_5_1_996 2 23 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 95 (accept_3_2 1 23 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 23 95))))))))))))))))))))))) (allB_succ 22 95 (allA_of_3_0 22 22 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 21 95 (allA_succ_of_accept 20 21 95 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 21 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 95 (accept_3_2 19 21 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 18
  21 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 95
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 21 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 95 (accept_3_2 16 21 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21
  95 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 21 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 21 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 21 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 95 (accept_3_2 13 21 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 21 95 (Polychromatic418967fa.accept_13_12_8_4_1_3099 12 21 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 95 (Polychromatic418967fa.accept_9_2_3_5_1_60 11
  21 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 95 (accept_3_2 10 21 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 95 (Polychromatic418967fa.accept_10_9_1_5_1_594 9
  21 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 95
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 21 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 95 (accept_3_2 7 21 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 95
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 21 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 95 (Polychromatic418967fa.accept_20_5_1_15_1_3928 5 21 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 95 (accept_3_2 4 21 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 21 95 (Polychromatic418967fa.accept_11_3_10_7_1_129 3 21 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 21
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 95 (accept_3_2 1 21 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 95))))))))))))))))))))) (allB_succ 20 95 (allA_succ_of_accept 19
  20 95 (accept_3_2 19 20 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 95
  (Polychromatic418967fa.accept_21_18_20_11_1_3927 18 20 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 20 95 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 20 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 95 (accept_3_2 16 20 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 20 95 5 3 4 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 20 95 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 20 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 95 (accept_3_2 13 20 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 95 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 20 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 20 95
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 20 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 20 95 5 2 4 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 20 95 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 20 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 95 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 20 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 95 (accept_3_2 7 20 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 95 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 20 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 20 95 5 1 4 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 20 95 (accept_3_2 4 20 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20 95 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 20 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 20 95
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 20 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 20 95 (accept_3_2 1 20 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20
  95)))))))))))))))))))) (allB_succ 19 95 (allA_of_3_0 19 19 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 18
  95 (allA_succ_of_accept 17 18 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 18 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 95 (accept_3_2 16 18 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 18 95 (Polychromatic418967fa.accept_13_2_5_4_1_3926 15 18 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 95 (Polychromatic418967fa.accept_13_1_5_4_1_463 14
  18 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 18 95 (accept_3_2 13 18 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 18 95 (Polychromatic418967fa.accept_10_2_8_5_1_587 12
  18 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 18 95
  (Polychromatic418967fa.accept_17_11_1_10_1_3925 11 18 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 18 95 (accept_3_2 10 18 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 18
  95 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 18 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 18 95 (Polychromatic418967fa.accept_14_8_4_11_1_3035 8 18 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 18 95 (accept_3_2 7 18 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 18 95 (Polychromatic418967fa.accept_13_6_5_4_1_3924 6 18 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 18 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 18
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 95 (accept_3_2 4 18 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 18 95 (Polychromatic418967fa.accept_10_3_8_5_1_606 3
  18 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 95
  (Polychromatic418967fa.accept_10_2_8_5_1_587 2 18 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 18 95 (accept_3_2 1 18 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18
  95)))))))))))))))))) (allB_succ 17 95 (allA_succ_of_accept 16 17 95 (accept_3_2 16 17 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 17 95 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 17 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 14
  17 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 95 (accept_3_2 13 17 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 17 95 (Polychromatic418967fa.accept_9_3_8_5_1_65 12
  17 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 95
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 17 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 17 95 (accept_3_2 10 17 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 17
  95 (Polychromatic418967fa.accept_23_9_17_3_1_3923 9 17 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 17 95 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 17 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 95 (accept_3_2 7 17 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 17 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 17 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 95 (Polychromatic418967fa.accept_16_5_1_15_1_3922 5
  17 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 95 (accept_3_2 4 17 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17 95 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 17
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 95
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 17 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 17 95 (accept_3_2 1 17 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17
  95))))))))))))))))) (allB_succ 16 95 (allA_of_3_0 16 16 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15 95
  (allA_succ_of_accept 14 15 95 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 15 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 95 (accept_3_2 13 15 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 15 95 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 15 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 95 (Polychromatic418967fa.accept_9_2_6_5_1_227 11
  15 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 15 95 5 2 3 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 15 95
  (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 15 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 15 95 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 15 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 95 (accept_3_2 7 15 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 15 95 (Polychromatic418967fa.accept_13_6_2_4_1_923 6 15 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 15 95 5 1 3 19 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 15 95 (accept_3_2 4 15 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 15 95 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 15 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 95 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 15
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 95 (accept_3_2 1 15 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 95))))))))))))))) (allB_succ 14 95 (allA_succ_of_accept 13 14 95
  (accept_3_2 13 14 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 95
  (Polychromatic418967fa.accept_21_12_14_11_1_3921 12 14 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 14 95 (Polychromatic418967fa.accept_10_1_4_5_1_1031 11 14 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 95 (accept_3_2 10 14 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 14 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 14 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 14 95 (Polychromatic418967fa.accept_12_8_2_11_1_246 8
  14 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 95 (accept_3_2 7 14 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 14 95 (Polychromatic418967fa.accept_10_6_4_5_1_615 6
  14 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 95
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 14 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 14 95 (accept_3_2 4 14 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14 95
  (Polychromatic418967fa.accept_6_3_2_5_1_32 3 14 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 14 95 (Polychromatic418967fa.accept_15_2_14_5_1_2072 2 14 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 95 (accept_3_2 1 14 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 95)))))))))))))) (allB_succ 13 95 (allA_of_3_0 13 13 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 12 95 (allA_succ_of_accept 11 12 95 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 12 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 95 (accept_3_2 10 12 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 12 95 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 12
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 95
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 12 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 12 95 (accept_3_2 7 12 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12 95
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 12 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 12 95 (Polychromatic418967fa.accept_13_5_12_4_1_449 5 12 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 95 (accept_3_2 4 12 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 12 95 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 12 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 12 95 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 12
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 95 (accept_3_2 1 12 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 95)))))))))))) (allB_succ 11 95 (allA_succ_of_accept 10 11 95
  (accept_3_2 10 11 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 95
  (Polychromatic418967fa.accept_10_9_1_5_1_594 9 11 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 95 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 11 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 95 (accept_3_2 7 11 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 95 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 11 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 95 (Polychromatic418967fa.accept_20_5_11_15_1_3920
  5 11 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 95 (accept_3_2 4 11 95
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 95 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 11
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 95
  (Polychromatic418967fa.accept_13_2_11_4_1_445 2 11 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 95 (accept_3_2 1 11 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11 95)))))))))))
  (allB_succ 10 95 (allA_of_3_0 10 10 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 95 (allA_succ_of_accept 8
  9 95 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 9 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 9 95 (accept_3_2 7 9 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 95
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 9 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 95 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 9 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 95 (accept_3_2 4 9 95 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 9 95 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 9 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 95 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 9 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 95 (accept_3_2 1 9 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 9 95))))))))) (allB_succ 8 95 (allA_succ_of_accept 7 8 95 (accept_3_2 7 8 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 95 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 8 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 8 95
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 8 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 8 95 (accept_3_2 4 8 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 8 95
  (Polychromatic418967fa.accept_6_3_2_5_1_32 3 8 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 8 95 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 8 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 95 (accept_3_2 1 8 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one
  8 95)))))))) (allB_succ 7 95 (allA_of_3_0 7 7 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 6 95
  (allA_succ_of_accept 5 6 95 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 6 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 6 95 (accept_3_2 4 6 95 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 6 95 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 6 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 2 6 95 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 6 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 95 (accept_3_2 1 6 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 6 95)))))) (allB_succ 5 95 (allA_succ_of_accept 4 5 95 (accept_3_2 4 5 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 95 (Polychromatic418967fa.accept_20_3_5_15_1_2644 3 5 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 95
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 5 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 95 (accept_3_2 1 5 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 95))))) (allB_succ
  4 95 (allA_of_3_0 4 4 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 3 95 (allA_succ_of_accept 2 3 95
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 3 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 95 (accept_3_2 1 3 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 95))) (allB_succ 2
  95 (allA_succ_of_accept 1 2 95 (accept_3_2 1 2 95 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 95)) (allB_two
  95)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


