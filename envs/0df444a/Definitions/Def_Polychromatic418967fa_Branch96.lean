-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch96
-- name    : Polychromatic418967fa_Branch96
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:09:47.905459+00:00
-- url     : https://prove2.me/theorems/d7cecdeb-42bd-414e-a439-16e871c64872
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

def Polychromatic418967fa.branch_96 : allB 96 96 :=
  allB_succ' 2 95 96 (Eq.refl Bool.true) (allA_succ_of_accept 1 95 96 (accept_3_4 1 95 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95 96)) (allB_succ' 3 94 96 (Eq.refl Bool.true) (allA_succ_of_gcd 2 94 96 2 1 47 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 94 96
  (Polychromatic418967fa.accept_7_1_3_5_1_33 1 94 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 94 96))) (allB_succ' 4 93 96 (Eq.refl Bool.true) (allA_succ_of_gcd 3 93 96 3 1 31 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 93 96
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 93 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 93 96 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 93 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 93 96)))) (allB_succ' 5 92 96 (Eq.refl Bool.true) (allA_succ_of_gcd 4 92 96
  4 1 23 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 92 96
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 92 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 92 96 2 1 46 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 92 96 (accept_3_4 1 92 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92 96)))))
  (allB_succ' 6 91 96 (Eq.refl Bool.true) (allA_succ_of_accept 5 91 96 (accept_3_5 5 91 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 91 96 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 91 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 96 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 91
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 96 (accept_3_5 2 91 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 96 (Polychromatic418967fa.accept_20_1_11_16_1_699 1
  91 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91 96)))))) (allB_succ' 7 90 96 (Eq.refl
  Bool.true) (allA_succ_of_gcd 6 90 96 6 1 15 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 90 96 (Polychromatic418967fa.accept_11_5_2_8_1_866 5 90 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 90 96 2 2 45 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 90 96 3 1 30 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 90 96 2 1 45 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 90 96 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 90
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90 96))))))) (allB_succ' 8 89 96 (Eq.refl
  Bool.true) (allA_succ_of_accept 7 89 96 (accept_3_4 7 89 96 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 89 96 (Polychromatic418967fa.accept_13_6_11_5_1_133 6 89 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 96 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 89 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 89 96 (accept_3_4 4 89 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89 96 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 89 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 89 96
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 89 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 89 96 (accept_3_4 1 89 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 89 96))))))))
  (allB_succ' 9 88 96 (Eq.refl Bool.true) (allA_succ_of_gcd 8 88 96 8 1 11 12 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 88 96 (Polychromatic418967fa.accept_15_7_13_6_1_696 7
  88 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 88 96 2 3 44 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 88 96 (accept_3_5 5 88
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 88 96 4 1 22 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 88 96
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 88 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 88 96 2 1 44 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 88 96 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 88 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 88 96))))))))) (allB_succ' 10 87 96 (Eq.refl Bool.true) (allA_succ_of_gcd 9
  87 96 3 3 29 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8
  87 96 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 87 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 96 (Polychromatic418967fa.accept_15_7_12_6_1_1327 7 87 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 87 96 3 2 29 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 87 96 (Polychromatic418967fa.accept_14_5_3_12_1_324 5 87 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 96
  (Polychromatic418967fa.accept_13_4_9_5_1_1641 4 87 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 87 96 3 1 29 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 87 96 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 87 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 96 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 87 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87 96)))))))))) (allB_succ' 11 86 96 (Eq.refl
  Bool.true) (allA_succ_of_gcd 10 86 96 2 5 43 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 86 96 (Polychromatic418967fa.accept_15_9_11_6_1_637 9 86 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 86 96 2 4 43 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 86 96 (accept_3_4 7 86 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 86 96 2 3 43 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 86 96 (Polychromatic418967fa.accept_15_5_11_6_1_692 5 86 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 86 96 2 2 43 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 86 96 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 86
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 86 96 2 1 43 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 86 96 (accept_3_4 1 86
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86 96))))))))))) (allB_succ' 12 85 96 (Eq.refl Bool.true)
  (allA_succ_of_accept 11 85 96 (accept_3_5 11 85 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 85
  96 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 85 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 85 96 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 85 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 96 (accept_3_5 8 85 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 85 96 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 85 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 96 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 85
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 85 96 (accept_3_5 5 85 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85 96 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 85
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 85 96
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 85 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 85 96 (accept_3_5 2 85 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 96
  (Polychromatic418967fa.accept_9_1_4_6_1_5 1 85 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 85 96)))))))))))) (allB_succ' 13 84 96 (Eq.refl Bool.true) (allA_succ_of_gcd 12 84 96 12 1 7 8 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 96
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 84 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 84 96 2 5 42 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 84 96 3 3 28 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 84 96 4 2 21 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 84 96 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 84 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 96 6 1 14 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 96 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 84 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 84 96 4 1 21 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 84 96 3 1 28 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 84 96 2 1 42 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 96
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 84 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 84 96))))))))))))) (allB_succ' 14 83 96 (Eq.refl Bool.true) (allA_succ_of_accept 13 83 96 (accept_3_4 13 83
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 96 (Polychromatic418967fa.accept_9_3_2_6_1_264
  12 83 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 96
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 83 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 96 (accept_3_4 10 83 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 83
  96 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 83 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 83 96 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 83 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 96 (accept_3_4 7 83 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 83 96 (Polychromatic418967fa.accept_14_6_13_12_1_810 6 83 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 96 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 83
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 83 96 (accept_3_4 4 83 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83 96 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 83
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 96
  (Polychromatic418967fa.accept_15_2_8_6_1_1340 2 83 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 83 96 (accept_3_4 1 83 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 83
  96)))))))))))))) (allB_succ' 15 82 96 (Eq.refl Bool.true) (allA_succ_of_gcd 14 82 96 2 7 41 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 82 96
  (Polychromatic418967fa.accept_9_4_1_6_1_284 13 82 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 82 96 2 6 41 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 82 96 (accept_3_5 11 82 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 82 96
  2 5 41 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 82 96
  (Polychromatic418967fa.accept_13_9_4_5_1_1651 9 82 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 82 96 2 4 41 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 82 96 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 82 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 82 96 2 3 41 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 82 96 (accept_3_5 5 82 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 82 96 2 2 41 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 82 96 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 82 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 82 96 2 1 41 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 82 96 (Polychromatic418967fa.accept_10_1_2_6_1_638 1 82
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82 96))))))))))))))) (allB_succ' 16 81 96
  (Eq.refl Bool.true) (allA_succ_of_gcd 15 81 96 3 5 27 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 81 96 (Polychromatic418967fa.accept_13_1_3_5_1_140 14 81 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 96
  (Polychromatic418967fa.accept_7_6_4_5_1_314 13 81 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 81 96 3 4 27 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 81 96 (Polychromatic418967fa.accept_13_11_3_5_1_982 11 81 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 96 (Polychromatic418967fa.accept_25_10_6_21_1_4078 10 81 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 81 96 3 3 27 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 81 96
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 81 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 81 96 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 81 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 81 96 3 2 27 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 81 96 (Polychromatic418967fa.accept_10_5_1_6_1_672 5 81 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 96
  (Polychromatic418967fa.accept_19_4_5_1_1_4077 4 81 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 81 96 3 1 27 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 81 96 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 81 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 96 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 81 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81 96)))))))))))))))) (allB_succ' 17 80 96
  (Eq.refl Bool.true) (allA_succ_of_gcd 16 80 96 16 1 5 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 80 96 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 80 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 80 96 2 7 40 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 80 96 (accept_3_4 13 80 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80 96 4 3 20 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 80 96 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 80 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 80 96 2 5 40 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 80 96
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 80 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 80 96 8 1 10 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 80 96 (accept_3_4 7 80 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 80 96 2
  3 40 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 80 96
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 80 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 80 96 4 1 20 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 80 96 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 80 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 80 96 2 1 40 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 80 96 (accept_3_4 1 80 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 80 96))))))))))))))))) (allB_succ' 18 79 96 (Eq.refl Bool.true) (allA_succ_of_accept 17 79 96
  (accept_3_5 17 79 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 79 96
  (Polychromatic418967fa.accept_11_5_2_8_1_866 16 79 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 79 96 (Polychromatic418967fa.accept_10_5_9_6_1_697 15 79 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 96 (accept_3_5 14 79 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 79 96 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 79 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 96 (Polychromatic418967fa.accept_9_3_7_6_1_76 12
  79 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 96 (accept_3_5 11 79 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 79 96 (Polychromatic418967fa.accept_7_3_2_5_1_147 10
  79 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 96
  (Polychromatic418967fa.accept_13_9_1_5_1_964 9 79 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 79 96 (accept_3_5 8 79 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 96
  (Polychromatic418967fa.accept_14_7_9_12_1_3975 7 79 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 79 96 (Polychromatic418967fa.accept_13_6_1_5_1_3988 6 79 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 96 (accept_3_5 5 79 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 79 96 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 79 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 96 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 79
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 96 (accept_3_5 2 79 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79 96 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 79
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79 96)))))))))))))))))) (allB_succ' 19 78 96
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 78 96 6 3 13 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 78 96 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 78 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 96 2 8 39 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 78 96 3 5 26 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 78 96 2 7 39 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 96
  (Polychromatic418967fa.accept_7_6_1_5_1_322 13 78 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 78 96 6 2 13 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 78 96 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 78 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 78 96 2 5 39 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 78 96 3 3 26 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 78 96 2 4 39 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 78 96 (Polychromatic418967fa.accept_19_7_2_1_1_4076 7 78 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 96 6 1 13 16 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 96
  (Polychromatic418967fa.accept_15_5_3_6_1_2128 5 78 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 78 96 2 2 39 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 78 96 3 1 26 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 78 96 2 1 39 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 78 96 (Polychromatic418967fa.accept_15_1_3_6_1_621 1 78 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 78 96))))))))))))))))))) (allB_succ' 20 77 96 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 77 96 (accept_3_4 19 77 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 77
  96 (Polychromatic418967fa.accept_21_18_14_12_1_4075 18 77 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 77 96 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 77 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 77 96 (accept_3_4 16 77 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 77 96 (Polychromatic418967fa.accept_13_2_12_5_1_1602 15 77 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 77 96
  (Polychromatic418967fa.accept_13_1_12_5_1_1601 14 77 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 77 96 (accept_3_4 13 77 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 77
  96 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 77 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 77 96 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 77 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 77 96 (accept_3_4 10 77 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 77 96 (Polychromatic418967fa.accept_14_9_7_12_1_4034 9 77 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 77 96 (Polychromatic418967fa.accept_9_8_5_6_1_538 8 77
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 96 (accept_3_4 7 77 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 96 (Polychromatic418967fa.accept_13_6_12_5_1_2304 6
  77 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 96
  (Polychromatic418967fa.accept_14_5_7_12_1_4006 5 77 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 96 (accept_3_4 4 77 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77 96
  (Polychromatic418967fa.accept_9_3_5_6_1_253 3 77 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 96 (Polychromatic418967fa.accept_9_2_5_6_1_536 2 77 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 96 (accept_3_4 1 77 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 96)))))))))))))))))))) (allB_succ' 21 76 96 (Eq.refl Bool.true) (allA_succ_of_gcd 20 76 96 4
  5 19 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 76 96
  (Polychromatic418967fa.accept_9_1_4_6_1_5 19 76 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 76 96 2 9 38 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 76 96 (accept_3_5 17 76 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 76 96
  4 4 19 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 76
  96 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 76 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 76 96 2 7 38 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 76 96 (Polychromatic418967fa.accept_14_13_6_12_1_3126 13 76 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 76 96 4 3 19 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 76 96 (accept_3_5 11 76 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 76 96 2 5 38 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 76 96 (Polychromatic418967fa.accept_11_9_10_8_1_444 9 76 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 76 96 4 2 19 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 76 96 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 76
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 76 96 2 3 38 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 76 96 (accept_3_5 5 76
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 76 96 4 1 19 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 76 96
  (Polychromatic418967fa.accept_9_3_4_6_1_252 3 76 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 76 96 2 1 38 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 76 96 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 76 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 76 96))))))))))))))))))))) (allB_succ' 22 75 96 (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 75 96 3 7 25 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 75 96 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 75 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 96 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 75 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 75 96 3 6 25 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 75 96
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 75 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 75 96 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 75 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 96 3 5 25 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 96 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 75 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 96
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 75 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 75 96 3 4 25 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 75 96 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 75 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 96 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 75 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 75 96 3 3 25 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 75 96
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 75 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 96 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 75 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 75 96 3 2 25 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 75 96 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 75 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 96
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 75 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 75 96 3 1 25 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 75 96 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 75 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 96 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 75 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75 96)))))))))))))))))))))) (allB_succ' 23 74
  96 (Eq.refl Bool.true) (allA_succ_of_gcd 22 74 96 2 11 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 74 96 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 74 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 74 96 2 10 37 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 74 96 (accept_3_4 19 74 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 74 96 2 9 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 74 96 (Polychromatic418967fa.accept_9_8_2_6_1_875 17
  74 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 74 96 2 8 37 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 74 96
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 74 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 74 96 2 7 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 74 96 (accept_3_4 13 74 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74 96
  2 6 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 74
  96 (Polychromatic418967fa.accept_25_11_24_21_1_4074 11 74 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 74 96 2 5 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 74 96 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 74 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 74 96 2 4 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 74 96 (accept_3_4 7 74 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 74 96 2 3 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 74 96 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 74 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 74 96 2 2 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 74 96 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 74
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 74 96 2 1 37 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 74 96 (accept_3_4 1 74
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74 96))))))))))))))))))))))) (allB_succ' 24 73 96 (Eq.refl
  Bool.true) (allA_succ_of_accept 23 73 96 (accept_3_5 23 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 73 96 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 73 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 73 96 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 73 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 96 (accept_3_5 20 73 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 96 (Polychromatic418967fa.accept_10_9_3_6_1_686 19
  73 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 96
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 96 (accept_3_5 17 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 73
  96 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 73 96 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 73 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 96 (accept_3_5 14 73 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 73 96 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 73 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 96 (Polychromatic418967fa.accept_9_3_1_6_1_86 12
  73 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 73 96 (accept_3_5 11 73 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 73 96 (Polychromatic418967fa.accept_13_10_8_5_1_1616
  10 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 73 96
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 73 96 (accept_3_5 8 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 96
  (Polychromatic418967fa.accept_9_7_1_6_1_261 7 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 73 96 (Polychromatic418967fa.accept_17_6_5_11_1_4073 6 73 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 73 96 (accept_3_5 5 73 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 73 96 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 73 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 73 96 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 73
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 96 (accept_3_5 2 73 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 96 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 73
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73 96)))))))))))))))))))))))) (allB_succ' 25
  72 96 (Eq.refl Bool.true) (allA_succ_of_gcd 24 72 96 24 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 96 (Polychromatic418967fa.accept_17_6_4_11_1_4072 23 72 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72 96 2 11 36 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 72 96 3 7 24 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 72 96 4 5 18 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 72 96
  (Polychromatic418967fa.accept_21_19_9_12_1_4071 19 72 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 72 96 6 3 12 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 72 96 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 72 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72 96 8 2 9 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 72 96 3 5 24 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 72 96 2 7 36 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 96 (Polychromatic418967fa.accept_21_13_9_12_1_4038 13 72 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 96 12 1 6 8 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 96
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 72 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 72 96 2 5 36 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 72 96 3 3 24 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 72 96 8 1 9 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 72 96 (Polychromatic418967fa.accept_14_7_2_12_1_1430 7 72 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 96 6 1 12 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 96 (Polychromatic418967fa.accept_15_5_12_6_1_639 5 72 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 96 4 1 18 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 72 96 3 1 24 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 72 96 2 1 36 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 96
  (Polychromatic418967fa.accept_10_1_2_6_1_638 1 72 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 72 96))))))))))))))))))))))))) (allB_succ' 26 71 96 (Eq.refl Bool.true) (allA_succ_of_accept 25 71 96
  (accept_3_4 25 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 96
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 71 96 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 71 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 71 96 (accept_3_4 22 71 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 71 96 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 71 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 71 96 (Polychromatic418967fa.accept_7_6_1_5_1_322 20
  71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 96 (accept_3_4 19 71 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 96 (Polychromatic418967fa.accept_7_4_1_5_1_540 18
  71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 96
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 96 (accept_3_4 16 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 71
  96 (Polychromatic418967fa.accept_10_5_1_6_1_672 15 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 71 96 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 71 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 96 (accept_3_4 13 71 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 71 96 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 71 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 96 (Polychromatic418967fa.accept_7_4_1_5_1_540 11
  71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 71 96 (accept_3_4 10 71 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 71 96 (Polychromatic418967fa.accept_15_9_11_6_1_637 9
  71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 96
  (Polychromatic418967fa.accept_27_8_17_15_1_4070 8 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 71 96 (accept_3_4 7 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 96
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 71 96 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 71 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 71 96 (accept_3_4 4 71 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 71 96 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 71 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 96 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 71
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 96 (accept_3_4 1 71 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 71 96)))))))))))))))))))))))))) (allB_succ' 27 70 96 (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 70 96 2 13 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 70 96 (Polychromatic418967fa.accept_17_8_2_11_1_4069 25 70 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 70 96 2 12 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 70 96 (accept_3_5 23 70 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 70 96 2 11 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 70 96 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 70 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 70 96 2 10 35 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 70 96
  (Polychromatic418967fa.accept_9_1_7_6_1_75 19 70 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 70 96 2 9 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 70 96 (accept_3_5 17 70 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 70 96
  2 8 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 70
  96 (Polychromatic418967fa.accept_18_15_16_6_1_1751 15 70 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 70 96 2 7 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 70 96 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 70 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 70 96 2 6 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 70 96 (accept_3_5 11 70 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70 96 2 5 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 70 96 (Polychromatic418967fa.accept_17_9_2_11_1_4042 9 70 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 70 96 2 4 35 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 70 96
  (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 70 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 70 96 2 3 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 70 96 (accept_3_5 5 70 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 70 96 2
  2 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 70 96
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 70 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 70 96 2 1 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 70 96 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 70 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 70 96))))))))))))))))))))))))))) (allB_succ' 28 69 96 (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 69 96 3 9 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 69 96 (Polychromatic418967fa.accept_15_11_9_6_1_1321 26 69 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 96 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 69 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 69 96 3 8 23 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 69 96
  (Polychromatic418967fa.accept_10_3_9_6_1_94 23 69 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 69 96 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 69 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 69 96 3 7 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 69 96 (Polychromatic418967fa.accept_14_6_13_12_1_810 20 69 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 96
  (Polychromatic418967fa.accept_13_6_4_5_1_2330 19 69 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 69 96 3 6 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 69 96 (Polychromatic418967fa.accept_11_6_3_8_1_843 17 69 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 96 (Polychromatic418967fa.accept_11_5_3_8_1_454 16 69 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 69 96 3 5 23 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 69 96
  (Polychromatic418967fa.accept_13_1_4_5_1_113 14 69 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 96 (Polychromatic418967fa.accept_10_3_9_6_1_94 13 69 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 69 96 3 4 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 69 96 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 69 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 96
  (Polychromatic418967fa.accept_13_10_4_5_1_2331 10 69 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 69 96 3 3 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 69 96 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 69 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 96 (Polychromatic418967fa.accept_17_7_1_11_1_1894 7 69 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 69 96 3 2 23 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 69 96
  (Polychromatic418967fa.accept_10_5_9_6_1_697 5 69 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 69 96 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 69 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 69 96 3 1 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 96 (Polychromatic418967fa.accept_13_2_4_5_1_3152 2 69 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 96
  (Polychromatic418967fa.accept_7_1_6_5_1_39 1 69 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 69 96)))))))))))))))))))))))))))) (allB_succ' 29 68 96 (Eq.refl Bool.true) (allA_succ_of_gcd 28 68 96 4 7 17
  24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 68 96
  (Polychromatic418967fa.accept_11_5_2_8_1_866 27 68 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 68 96 2 13 34 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 68 96 (accept_3_4 25 68 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 68 96
  4 6 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 68
  96 (Polychromatic418967fa.accept_10_3_8_6_1_326 23 68 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 68 96 2 11 34 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 68 96 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 68 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 68 96 4 5 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 68 96 (accept_3_4 19 68 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 68 96 2 9 34 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 68 96 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 68 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 68 96 4 4 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 68 96 (Polychromatic418967fa.accept_13_2_3_5_1_2294 15
  68 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 68 96 2 7 34 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 68 96 (accept_3_4 13 68
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68 96 4 3 17 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 68 96
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 68 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 68 96 2 5 34 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 68 96 (Polychromatic418967fa.accept_13_9_3_5_1_1605 9 68 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 68 96 4 2 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 68 96 (accept_3_4 7 68 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 68 96 2 3 34 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 68 96 (Polychromatic418967fa.accept_11_5_2_8_1_866 5 68 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 68 96 4 1 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 68 96 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 68
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 68 96 2 1 34 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 68 96 (accept_3_4 1 68
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68 96))))))))))))))))))))))))))))) (allB_succ' 30 67 96 (Eq.refl
  Bool.true) (allA_succ_of_accept 29 67 96 (accept_3_5 29 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 67 96 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 67 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 67 96 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 67 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 96 (accept_3_5 26 67 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 96 (Polychromatic418967fa.accept_9_7_4_6_1_273 25
  67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 96
  (Polychromatic418967fa.accept_21_3_4_12_1_1462 24 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 96 (accept_3_5 23 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 67
  96 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 67 96 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 67 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 96 (accept_3_5 20 67 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 67 96 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 67 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 96 (Polychromatic418967fa.accept_21_18_4_12_1_4068
  18 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 67 96 (accept_3_5 17 67
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 67 96 (Polychromatic418967fa.accept_7_2_4_5_1_313
  16 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 67 96
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 67 96 (accept_3_5 14 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 67
  96 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 67 96 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 67 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 67 96 (accept_3_5 11 67 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 67 96 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 67 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 67 96 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 67
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 96 (accept_3_5 8 67 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 96 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 67
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 96
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 96 (accept_3_5 5 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67 96
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 4 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 96 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 67 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 96 (accept_3_5 2 67 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 96 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 67 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67 96)))))))))))))))))))))))))))))) (allB_succ' 31 66 96 (Eq.refl
  Bool.true) (allA_succ_of_gcd 30 66 96 6 5 11 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 66 96 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 66 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66 96 2 14 33 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 66 96 3 9 22 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 66 96 2 13 33 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 66 96 (Polychromatic418967fa.accept_9_7_3_6_1_270 25
  66 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 96 6 4 11 16 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 96
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 66 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 66 96 2 11 33 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 66 96 3 7 22 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 66 96 2 10 33 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 66 96 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 66 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 96 6 3 11 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 96 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 66 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66 96 2 8 33 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 66 96 3 5 22 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 66 96 2 7 33 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 96
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 66 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 66 96 6 2 11 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 66 96 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 66 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66 96 2 5 33 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 66 96 3 3 22 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 66 96 2 4 33 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 96 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 66 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 96 6 1 11 16 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 96
  (Polychromatic418967fa.accept_9_5_3_6_1_269 5 66 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 66 96 2 2 33 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 66 96 3 1 22 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 66 96 2 1 33 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 66 96 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 66 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 66 96))))))))))))))))))))))))))))))) (allB_succ' 32 65 96 (Eq.refl
  Bool.true) (allA_succ_of_accept 31 65 96 (accept_3_4 31 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 65 96 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 65 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 96 (Polychromatic418967fa.accept_10_9_5_6_1_691 29 65 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 96 (accept_3_4 28 65 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 96 (Polychromatic418967fa.accept_15_12_5_6_1_2148
  27 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 65 96
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 65 96 (accept_3_4 25 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 65
  96 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 65 96 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 65 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 96 (accept_3_4 22 65 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 65 96 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 65 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 65 96 (Polychromatic418967fa.accept_11_9_10_8_1_444
  20 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 96 (accept_3_4 19 65
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 96 (Polychromatic418967fa.accept_7_4_2_5_1_527
  18 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 96
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 96 (accept_3_4 16 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 65
  96 (Polychromatic418967fa.accept_18_15_11_6_1_4067 15 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 96 (Polychromatic418967fa.accept_9_5_2_6_1_265 14 65 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 96 (accept_3_4 13 65 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 96 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 65 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 96
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 96 (accept_3_4 10 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 65
  96 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 65 96 (Polychromatic418967fa.accept_9_8_2_6_1_875 8 65 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 96 (accept_3_4 7 65 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 65 96 (Polychromatic418967fa.accept_21_6_2_12_1_4066 6 65 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 96 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 65
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 65 96 (accept_3_4 4 65 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65 96 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 65
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 96
  (Polychromatic418967fa.accept_19_2_8_1_1_4065 2 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 65 96 (accept_3_4 1 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65
  96)))))))))))))))))))))))))))))))) (allB_succ' 33 64 96 (Eq.refl Bool.true) (allA_succ_of_gcd 32 64 96 32 1 2 3
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 64 96
  (Polychromatic418967fa.accept_7_3_1_5_1_44 31 64 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 64 96 2 15 32 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 64 96 (accept_3_5 29 64 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 64 96
  4 7 16 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 64
  96 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 64 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 64 96 2 13 32 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 64 96 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 64 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 64 96 8 3 8 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 64 96 (accept_3_5 23 64 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 64 96 2 11 32 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 64 96 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 64 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 64 96 4 5 16 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 64 96 (Polychromatic418967fa.accept_13_6_12_5_1_2304
  19 64 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 64 96 2 9 32 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 64 96 (accept_3_5 17 64
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 64 96 16 1 4 6 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 64 96
  (Polychromatic418967fa.accept_10_5_4_6_1_319 15 64 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 64 96 2 7 32 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 64 96 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 64 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 64 96 4 3 16 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 64 96 (accept_3_5 11 64 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 64 96 2 5 32 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 64 96 (Polychromatic418967fa.accept_15_9_4_6_1_3075 9 64 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 64 96 8 1 8 12 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 64 96 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 64
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 64 96 2 3 32 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 64 96 (accept_3_5 5 64
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 64 96 4 1 16 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 64 96
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 64 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 64 96 2 1 32 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 64 96 (Polychromatic418967fa.accept_13_1_12_5_1_1601 1 64 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 64 96))))))))))))))))))))))))))))))))) (allB_succ' 34 63 96 (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 63 96 3 11 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 63 96 (Polychromatic418967fa.accept_13_6_11_5_1_133 32 63 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 96 (Polychromatic418967fa.accept_15_1_3_6_1_621 31
  63 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 63 96 3 10 21 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 63 96
  (Polychromatic418967fa.accept_10_9_3_6_1_686 29 63 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 63 96 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 63 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 63 96 3 9 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 63 96 (Polychromatic418967fa.accept_15_11_3_6_1_1306 26 63 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 96
  (Polychromatic418967fa.accept_15_10_3_6_1_3042 25 63 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 63 96 3 8 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 63 96 (Polychromatic418967fa.accept_14_9_7_12_1_4034 23 63 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 96 (Polychromatic418967fa.accept_19_3_6_1_1_4064 22 63 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63 96 3 7 21 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 63 96
  (Polychromatic418967fa.accept_13_7_11_5_1_2302 20 63 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 96 (Polychromatic418967fa.accept_10_9_3_6_1_686 19 63 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 63 96 3 6 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 63 96 (Polychromatic418967fa.accept_10_7_3_6_1_644 17 63 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 96
  (Polychromatic418967fa.accept_13_3_11_5_1_2348 16 63 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 63 96 3 5 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 63 96 (Polychromatic418967fa.accept_17_14_12_11_1_4063 14 63 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 96 (Polychromatic418967fa.accept_17_13_12_11_1_2947 13 63
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 63 96 3 4 21 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 63 96
  (Polychromatic418967fa.accept_15_11_3_6_1_1306 11 63 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 63 96 (Polychromatic418967fa.accept_15_10_3_6_1_3042 10 63 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 63 96 3 3 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 63 96 (Polychromatic418967fa.accept_10_8_3_6_1_685 8 63 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 96
  (Polychromatic418967fa.accept_10_7_3_6_1_644 7 63 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 63 96 3 2 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 63 96 (Polychromatic418967fa.accept_14_5_7_12_1_4006 5 63 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 96 (Polychromatic418967fa.accept_26_4_11_18_1_4062 4 63 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 63 96 3 1 21 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 63 96
  (Polychromatic418967fa.accept_14_2_7_12_1_1485 2 63 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 63 96 (Polychromatic418967fa.accept_15_1_3_6_1_621 1 63 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 63 96)))))))))))))))))))))))))))))))))) (allB_succ' 35 62 96 (Eq.refl
  Bool.true) (allA_succ_of_gcd 34 62 96 2 17 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 62 96 (Polychromatic418967fa.accept_23_10_16_4_1_4061 33 62 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 62 96 2 16 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 62 96 (accept_3_4 31 62 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 62 96 2 15 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 62 96 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 62 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 62 96 2 14 31 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 62 96
  (Polychromatic418967fa.accept_14_13_6_12_1_3126 27 62 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 62 96 2 13 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 62 96 (accept_3_4 25 62 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 62 96
  2 12 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 62
  96 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 62 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 62 96 2 11 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 62 96 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 62 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 62 96 2 10 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 62 96 (accept_3_4 19 62 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 62 96 2 9 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 62 96 (Polychromatic418967fa.accept_13_4_10_5_1_1644 17 62 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 96 2 8 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 96 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 62
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 62 96 2 7 31 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 62 96 (accept_3_4 13 62
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62 96 2 6 31 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 62 96
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 62 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 62 96 2 5 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 62 96 (Polychromatic418967fa.accept_18_9_8_6_1_4021 9 62 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 96 2 4 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 96 (accept_3_4 7 62 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 62 96 2 3 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 62 96 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 62 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 96 2 2 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 96 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 62
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 62 96 2 1 31 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 62 96 (accept_3_4 1 62
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62 96))))))))))))))))))))))))))))))))))) (allB_succ' 36 61 96
  (Eq.refl Bool.true) (allA_succ_of_accept 35 61 96 (accept_3_5 35 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 61 96 (Polychromatic418967fa.accept_19_15_4_1_1_4060 34 61 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 61 96 (Polychromatic418967fa.accept_15_3_1_6_1_206 33 61 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 96 (accept_3_5 32 61 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 96 (Polychromatic418967fa.accept_9_4_7_6_1_255 31
  61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 96
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 96 (accept_3_5 29 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 61
  96 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 61 96 (Polychromatic418967fa.accept_10_7_1_6_1_673 27 61 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 96 (accept_3_5 26 61 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 61 96 (Polychromatic418967fa.accept_10_5_1_6_1_672 25 61 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 96 (Polychromatic418967fa.accept_14_10_5_12_1_3995
  24 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 61 96 (accept_3_5 23 61
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 61 96 (Polychromatic418967fa.accept_9_4_7_6_1_255
  22 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 61 96
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 61 96 (accept_3_5 20 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 61
  96 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 61 96 (Polychromatic418967fa.accept_15_3_1_6_1_206 18 61 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 61 96 (accept_3_5 17 61 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 61 96 (Polychromatic418967fa.accept_13_3_9_5_1_2340 16 61 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 61 96 (Polychromatic418967fa.accept_10_5_1_6_1_672 15
  61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 96 (accept_3_5 14 61 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 96 (Polychromatic418967fa.accept_9_4_7_6_1_255 13
  61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 96
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 96 (accept_3_5 11 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 61
  96 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 61 96 (Polychromatic418967fa.accept_15_9_1_6_1_657 9 61 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 96 (accept_3_5 8 61 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 61 96 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 61 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 96 (Polychromatic418967fa.accept_20_6_1_16_1_4059 6
  61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 61 96 (accept_3_5 5 61 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61 96 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 61
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 61 96
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 61 96 (accept_3_5 2 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 61 96
  (Polychromatic418967fa.accept_9_1_7_6_1_75 1 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 61 96)))))))))))))))))))))))))))))))))))) (allB_succ' 37 60 96 (Eq.refl Bool.true) (allA_succ_of_gcd 36 60
  96 12 3 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60
  96 (Polychromatic418967fa.accept_11_2_5_8_1_470 35 60 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 60 96 2 17 30 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 60 96 3 11 20 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 60 96 4 8 15 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 60 96 (Polychromatic418967fa.accept_22_9_16_8_1_4058 31 60 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 96 6 5 10 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 96 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 60 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60 96 4 7 15 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 60 96 3 9 20 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 60 96 2 13 30 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 60 96
  (Polychromatic418967fa.accept_11_3_5_8_1_458 25 60 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 60 96 12 2 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 60 96 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 60 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 96 2 11 30 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 60 96 3 7 20 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 60 96 4 5 15 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 96 (Polychromatic418967fa.accept_17_2_9_11_1_4057 19 60 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 96 6 3 10 16 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 96
  (Polychromatic418967fa.accept_19_17_3_1_1_4056 17 60 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 60 96 4 4 15 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 60 96 3 5 20 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 60 96 2 7 30 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 60 96 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 60 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 96 12 1 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 96 (Polychromatic418967fa.accept_19_11_3_1_1_2799 11 60 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 96 2 5 30 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 60 96 3 3 20 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 60 96 4 2 15 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 96
  (Polychromatic418967fa.accept_21_7_18_12_1_1493 7 60 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 60 96 6 1 10 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 60 96 (Polychromatic418967fa.accept_19_5_3_1_1_4055 5 60 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 96 4 1 15 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 60 96 3 1 20 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 60 96 2 1 30 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 96 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 60 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60 96)))))))))))))))))))))))))))))))))))))
  (allB_succ' 38 59 96 (Eq.refl Bool.true) (allA_succ_of_accept 37 59 96 (accept_3_4 37 59 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 96 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 59 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 96
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 96 (accept_3_4 34 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 59
  96 (Polychromatic418967fa.accept_10_3_9_6_1_94 33 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 59 96 (Polychromatic418967fa.accept_19_13_2_1_1_4054 32 59 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 96 (accept_3_4 31 59 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 59 96 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 59 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 96 (Polychromatic418967fa.accept_7_1_3_5_1_33 29
  59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 59 96 (accept_3_4 28 59 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 59 96 (Polychromatic418967fa.accept_19_8_2_1_1_4053
  27 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 59 96
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 59 96 (accept_3_4 25 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 59
  96 (Polychromatic418967fa.accept_13_11_7_5_1_2314 24 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 59 96 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 59 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 59 96 (accept_3_4 22 59 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 59 96 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 59 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 59 96
  (Polychromatic418967fa.accept_9_2_5_6_1_536 20 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 59 96 (accept_3_4 19 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 59
  96 (Polychromatic418967fa.accept_11_7_4_8_1_1371 18 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 59 96 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 59 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 59 96 (accept_3_4 16 59 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 59 96 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 59 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 59 96 (Polychromatic418967fa.accept_17_14_8_11_1_4052
  14 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 96 (accept_3_4 13 59
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 96 (Polychromatic418967fa.accept_9_3_5_6_1_253
  12 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 96
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 96 (accept_3_4 10 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 59
  96 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 59 96 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 59 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 96 (accept_3_4 7 59 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 59 96 (Polychromatic418967fa.accept_19_6_2_1_1_4051 6 59 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 96 (Polychromatic418967fa.accept_10_5_9_6_1_697 5
  59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 96 (accept_3_4 4 59 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59 96 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 59
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 96
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 59 96 (accept_3_4 1 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59
  96)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 58 96 (Eq.refl Bool.true) (allA_succ_of_gcd 38 58 96 2 19 29
  48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 58 96
  (Polychromatic418967fa.accept_9_1_4_6_1_5 37 58 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 58 96 2 18 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 58 96 (accept_3_5 35 58 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 58 96
  2 17 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 58
  96 (Polychromatic418967fa.accept_10_3_8_6_1_326 33 58 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 58 96 2 16 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 58 96 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 58 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 58 96 2 15 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 58 96 (accept_3_5 29 58 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 58 96 2 14 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 58 96 (Polychromatic418967fa.accept_11_5_3_8_1_454 27 58 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 58 96 2 13 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 58 96 (Polychromatic418967fa.accept_7_4_2_5_1_527 25
  58 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 58 96 2 12 29 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 58 96 (accept_3_5 23 58
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 58 96 2 11 29 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 58 96
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 58 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 58 96 2 10 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 58 96 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 58 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 58 96 2 9 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 58 96 (accept_3_5 17 58 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 58 96 2 8 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 58 96 (Polychromatic418967fa.accept_18_15_4_6_1_1763 15 58 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 58 96 2 7 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 58 96 (Polychromatic418967fa.accept_10_3_8_6_1_326 13
  58 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 58 96 2 6 29 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 58 96 (accept_3_5 11 58
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58 96 2 5 29 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 58 96
  (Polychromatic418967fa.accept_21_9_16_12_1_4050 9 58 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 58 96 2 4 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 58 96 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 58 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 96 2 3 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 96 (accept_3_5 5 58 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 58 96 2 2 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 58 96 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 58 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 58 96 2 1 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 58 96 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 58 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58 96)))))))))))))))))))))))))))))))))))))))
  (allB_succ' 40 57 96 (Eq.refl Bool.true) (allA_succ_of_gcd 39 57 96 3 13 19 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 57 96 (Polychromatic418967fa.accept_7_3_1_5_1_44 38 57
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 96
  (Polychromatic418967fa.accept_9_1_3_6_1_70 37 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 57 96 3 12 19 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 57 96 (Polychromatic418967fa.accept_9_8_3_6_1_533 35 57 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 96 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 57 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 57 96 3 11 19 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 57 96
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 96 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 57 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 57 96 3 10 19 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 57 96 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 57 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 96
  (Polychromatic418967fa.accept_9_1_3_6_1_70 28 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 57 96 3 9 19 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 57 96 (Polychromatic418967fa.accept_9_8_3_6_1_533 26 57 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 96 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 57 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 57 96 3 8 19 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 57 96
  (Polychromatic418967fa.accept_9_5_3_6_1_269 23 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 57 96 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 57 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 57 96 3 7 19 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 57 96 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 57 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 96
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 57 96 3 6 19 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 57 96 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 57 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 96 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 57 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 57 96 3 5 19 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 57 96
  (Polychromatic418967fa.accept_9_5_3_6_1_269 14 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 96 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 57 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 57 96 3 4 19 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 57 96 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 57 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 96
  (Polychromatic418967fa.accept_7_3_1_5_1_44 10 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 57 96 3 3 19 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 57 96 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 57 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 96 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 57 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 57 96 3 2 19 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 57 96
  (Polychromatic418967fa.accept_9_5_3_6_1_269 5 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 57 96 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 57 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 57 96 3 1 19 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 57 96 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 57 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 96
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 57 96)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 56 96 (Eq.refl Bool.true) (allA_succ_of_gcd 40
  56 96 8 5 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  56 96 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 56 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 56 96 2 19 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 56 96 (accept_3_4 37 56 96 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 56 96 4 9 14 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 56 96 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 56 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 56 96 2 17 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 56 96 (Polychromatic418967fa.accept_15_3_11_6_1_3083 33 56 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 56 96 8 4 7 12 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 56 96 (accept_3_4 31 56 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 56 96 2 15 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 56 96 (Polychromatic418967fa.accept_21_8_14_12_1_4049
  29 56 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 56 96 4 7 14 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 56 96
  (Polychromatic418967fa.accept_13_1_4_5_1_113 27 56 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 56 96 2 13 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 56 96 (accept_3_4 25 56 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 56 96
  8 3 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 56 96
  (Polychromatic418967fa.accept_9_5_2_6_1_265 23 56 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 56 96 2 11 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 56 96 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 56 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 56 96 4 5 14 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 56 96 (accept_3_4 19 56 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 56 96 2 9 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 56 96 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 56 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 56 96 8 2 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 56 96 (Polychromatic418967fa.accept_11_4_1_8_1_1366 15
  56 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 96 2 7 28 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 96 (accept_3_4 13 56
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56 96 4 3 14 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 56 96
  (Polychromatic418967fa.accept_19_11_18_1_1_4048 11 56 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 56 96 2 5 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 56 96 (Polychromatic418967fa.accept_13_9_4_5_1_1651 9 56 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 56 96 8 1 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 56 96 (accept_3_4 7 56 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 56 96 2 3 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 56 96 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 56 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 56 96 4 1 14 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 56 96 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 56
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 56 96 2 1 28 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 56 96 (accept_3_4 1 56
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 96))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 55
  96 (Eq.refl Bool.true) (allA_succ_of_accept 41 55 96 (accept_3_5 41 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 55 96 (Polychromatic418967fa.accept_9_4_1_6_1_284 40 55 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 55 96 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 55 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 96 (accept_3_5 38 55 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 96 (Polychromatic418967fa.accept_13_11_3_5_1_982
  37 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 96
  (Polychromatic418967fa.accept_7_1_6_5_1_39 36 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 55 96 (accept_3_5 35 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 55
  96 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 55 96 (Polychromatic418967fa.accept_15_3_10_6_1_632 33 55 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 96 (accept_3_5 32 55 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 55 96 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 55 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 96 (Polychromatic418967fa.accept_9_3_1_6_1_86 30
  55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 55 96 (accept_3_5 29 55 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 96 (Polychromatic418967fa.accept_13_2_3_5_1_2294
  28 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 96
  (Polychromatic418967fa.accept_13_1_3_5_1_140 27 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 96 (accept_3_5 26 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 55
  96 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 55 96 (Polychromatic418967fa.accept_10_4_5_6_1_651 24 55 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 96 (accept_3_5 23 55 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 55 96 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 55 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 96 (Polychromatic418967fa.accept_9_3_1_6_1_86 21
  55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 96 (accept_3_5 20 55 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 96 (Polychromatic418967fa.accept_10_9_5_6_1_691 19
  55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 96
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 96 (accept_3_5 17 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 55
  96 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 55 96 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 55 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 96 (accept_3_5 14 55 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 55 96 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 55 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 96 (Polychromatic418967fa.accept_9_3_1_6_1_86 12
  55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 96 (accept_3_5 11 55 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 55 96 (Polychromatic418967fa.accept_17_10_4_11_1_4047
  10 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 96
  (Polychromatic418967fa.accept_10_9_5_6_1_691 9 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 55 96 (accept_3_5 8 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 96
  (Polychromatic418967fa.accept_9_7_1_6_1_261 7 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 55 96 (Polychromatic418967fa.accept_13_6_3_5_1_3167 6 55 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 55 96 (accept_3_5 5 55 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 55 96 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 55 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 96 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 55
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 96 (accept_3_5 2 55 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 96 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 55
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55
  96)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 54 96 (Eq.refl Bool.true) (allA_succ_of_gcd 42 54 96 6 7 9
  16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 96
  (Polychromatic418967fa.accept_15_11_9_6_1_1321 41 54 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 54 96 2 20 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 54 96 3 13 18 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 38 54 96 2 19 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 54 96 (Polychromatic418967fa.accept_28_9_26_12_1_4046 37 54 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 96 6 6 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 96 (Polychromatic418967fa.accept_10_5_4_6_1_319 35 54 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 54 96 2 17 27 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 54 96 3 11 18 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 54 96 2 16 27 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 96
  (Polychromatic418967fa.accept_11_9_10_8_1_444 31 54 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 54 96 6 5 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 54 96 (Polychromatic418967fa.accept_13_3_2_5_1_1632 29 54 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 96 2 14 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 54 96 3 9 18 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 54 96 2 13 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 54 96 (Polychromatic418967fa.accept_10_5_4_6_1_319 25 54 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 96 6 4 9 16 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 96
  (Polychromatic418967fa.accept_13_10_2_5_1_1633 23 54 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 54 96 2 11 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 54 96 3 7 18 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 54 96 2 10 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 54 96 (Polychromatic418967fa.accept_15_4_9_6_1_627 19 54 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 96 6 3 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 96 (Polychromatic418967fa.accept_13_4_2_5_1_4045 17 54 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 96 2 8 27 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 54 96 3 5 18 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 54 96 2 7 27 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 96
  (Polychromatic418967fa.accept_19_13_16_1_1_4044 13 54 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 54 96 6 2 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 54 96 (Polychromatic418967fa.accept_15_11_9_6_1_1321 11 54 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54 96 2 5 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 54 96 3 3 18 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 54 96 2 4 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 96 (Polychromatic418967fa.accept_13_7_2_5_1_2344 7 54 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 96 6 1 9 16 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 96
  (Polychromatic418967fa.accept_10_5_4_6_1_319 5 54 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 54 96 2 2 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 54 96 3 1 18 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 54 96 2 1 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 54 96 (Polychromatic418967fa.accept_15_1_9_6_1_1323 1 54 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 54 96))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 53 96
  (Eq.refl Bool.true) (allA_succ_of_accept 43 53 96 (accept_3_4 43 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 53 96 (Polychromatic418967fa.accept_13_3_1_5_1_499 42 53 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 96 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 53 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 96 (accept_3_4 40 53 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 96 (Polychromatic418967fa.accept_9_3_8_6_1_80 39
  53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 53 96
  (Polychromatic418967fa.accept_9_2_8_6_1_79 38 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 53 96 (accept_3_4 37 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 53
  96 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 53 96 (Polychromatic418967fa.accept_13_9_1_5_1_964 35 53 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 53 96 (accept_3_4 34 53 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 53 96 (Polychromatic418967fa.accept_18_15_17_6_1_4043 33 53 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 53 96 (Polychromatic418967fa.accept_9_5_8_6_1_281 32
  53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 96 (accept_3_4 31 53 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 96 (Polychromatic418967fa.accept_7_2_4_5_1_313 30
  53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 96
  (Polychromatic418967fa.accept_7_1_4_5_1_35 29 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 96 (accept_3_4 28 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 53
  96 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 53 96 (Polychromatic418967fa.accept_17_9_2_11_1_4042 26 53 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 96 (accept_3_4 25 53 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 53 96 (Polychromatic418967fa.accept_19_5_15_1_1_4041 24 53 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 96 (Polychromatic418967fa.accept_7_2_4_5_1_313 23
  53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 53 96 (accept_3_4 22 53 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 53 96 (Polychromatic418967fa.accept_9_3_8_6_1_80 21
  53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 53 96
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 53 96 (accept_3_4 19 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 53
  96 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 53 96 (Polychromatic418967fa.accept_10_7_3_6_1_644 17 53 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 96 (accept_3_4 16 53 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 53 96 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 53 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 96 (Polychromatic418967fa.accept_9_5_8_6_1_281 14
  53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 96 (accept_3_4 13 53 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 96 (Polychromatic418967fa.accept_9_3_8_6_1_80 12
  53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 96
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 96 (accept_3_4 10 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 53
  96 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 53 96 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 53 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 96 (accept_3_4 7 53 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 53 96 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 53 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 96 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 53
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 53 96 (accept_3_4 4 53 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53 96 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 53
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 53 96
  (Polychromatic418967fa.accept_7_2_4_5_1_313 2 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 53 96 (accept_3_4 1 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 53
  96)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 52 96 (Eq.refl Bool.true) (allA_succ_of_gcd 44 52 96 4
  11 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 52 96
  (Polychromatic418967fa.accept_7_1_3_5_1_33 43 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 52 96 2 21 26 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 52 96 (accept_3_5 41 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 52 96
  4 10 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 52
  96 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 52 96 2 19 26 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 52 96 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 52 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 52 96 4 9 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 52 96 (accept_3_5 35 52 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 52 96 2 17 26 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 52 96 (Polychromatic418967fa.accept_14_5_10_12_1_1454 33 52 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 52 96 4 8 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 52 96 (Polychromatic418967fa.accept_9_4_7_6_1_255 31
  52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 52 96 2 15 26 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 52 96 (accept_3_5 29 52
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 52 96 4 7 13 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 52 96
  (Polychromatic418967fa.accept_15_12_7_6_1_4013 27 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 52 96 2 13 26 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 52 96 (Polychromatic418967fa.accept_17_8_1_11_1_4004 25 52 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 52 96 4 6 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 52 96 (accept_3_5 23 52 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 52 96 2 11 26 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 52 96 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 52 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 52 96 4 5 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 52 96 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 52
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 52 96 2 9 26 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 52 96 (accept_3_5 17 52
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52 96 4 4 13 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 52 96
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 52 96 2 7 26 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 52 96 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 52 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 52 96 4 3 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 52 96 (accept_3_5 11 52 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 52 96 2 5 26 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 52 96 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 52 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 52 96 4 2 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 52 96 (Polychromatic418967fa.accept_17_7_1_11_1_1894 7
  52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 52 96 2 3 26 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 52 96 (accept_3_5 5 52
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 52 96 4 1 13 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 52 96
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 52 96 2 1 26 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 52 96 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 52 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 52 96))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 51 96
  (Eq.refl Bool.true) (allA_succ_of_gcd 45 51 96 3 15 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 51 96 (Polychromatic418967fa.accept_21_2_9_12_1_4040 44 51 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 96
  (Polychromatic418967fa.accept_13_4_12_5_1_476 43 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 51 96 3 14 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 51 96 (Polychromatic418967fa.accept_13_2_12_5_1_1602 41 51 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 96 (Polychromatic418967fa.accept_13_1_12_5_1_1601 40 51 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 51 96 3 13 17 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 51 96
  (Polychromatic418967fa.accept_7_3_2_5_1_147 38 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 96 (Polychromatic418967fa.accept_10_7_1_6_1_673 37 51 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 51 96 3 12 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 51 96 (Polychromatic418967fa.accept_10_5_1_6_1_672 35 51 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 96
  (Polychromatic418967fa.accept_13_8_12_5_1_1604 34 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 51 96 3 11 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 51 96 (Polychromatic418967fa.accept_7_4_2_5_1_527 32 51 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 96 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 51 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 51 96 3 10 17 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 51 96
  (Polychromatic418967fa.accept_18_11_15_6_1_2832 29 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 51 96 (Polychromatic418967fa.accept_13_2_12_5_1_1602 28 51 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 51 96 3 9 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 51 96 (Polychromatic418967fa.accept_11_4_7_8_1_1926 26 51 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 96
  (Polychromatic418967fa.accept_7_4_2_5_1_527 25 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 51 96 3 8 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 51 96 (Polychromatic418967fa.accept_18_5_15_6_1_3999 23 51 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 96 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 51 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 51 96 3 7 17 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 51 96
  (Polychromatic418967fa.accept_13_7_12_5_1_1603 20 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 96 (Polychromatic418967fa.accept_13_6_12_5_1_2304 19 51 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 51 96 3 6 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 51 96 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 51 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 96
  (Polychromatic418967fa.accept_18_16_15_6_1_4039 16 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 51 96 3 5 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 51 96 (Polychromatic418967fa.accept_13_1_12_5_1_1601 14 51 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 96 (Polychromatic418967fa.accept_21_13_9_12_1_4038 13 51 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 51 96 3 4 17 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 51 96
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 51 96 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 51 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 51 96 3 3 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 51 96 (Polychromatic418967fa.accept_13_8_12_5_1_1604 8 51 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 96
  (Polychromatic418967fa.accept_10_7_1_6_1_673 7 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 51 96 3 2 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 51 96 (Polychromatic418967fa.accept_10_5_1_6_1_672 5 51 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 96 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 51 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 51 96 3 1 17 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 51 96
  (Polychromatic418967fa.accept_10_2_1_6_1_634 2 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 51 96 (Polychromatic418967fa.accept_13_1_12_5_1_1601 1 51 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 51 96)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 50 96
  (Eq.refl Bool.true) (allA_succ_of_gcd 46 50 96 2 23 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 50 96 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 50 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 50 96 2 22 25 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 50 96 (accept_3_4 43 50 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 50 96 2 21 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 50 96 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 50 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 50 96 2 20 25 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 50 96
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 50 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 50 96 2 19 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 50 96 (accept_3_4 37 50 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 50 96
  2 18 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 50
  96 (Polychromatic418967fa.accept_9_8_5_6_1_538 35 50 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 50 96 2 17 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 50 96 (Polychromatic418967fa.accept_13_7_11_5_1_2302 33 50 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 50 96 2 16 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 50 96 (accept_3_4 31 50 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 50 96 2 15 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 50 96 (Polychromatic418967fa.accept_9_2_5_6_1_536 29 50 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 50 96 2 14 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 50 96 (Polychromatic418967fa.accept_7_6_1_5_1_322 27
  50 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 50 96 2 13 25 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 50 96 (accept_3_4 25 50
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 50 96 2 12 25 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 50 96
  (Polychromatic418967fa.accept_19_4_12_1_1_3991 23 50 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 50 96 2 11 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 50 96 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 50 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 96 2 10 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 96 (accept_3_4 19 50 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 50 96 2 9 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 50 96 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 50 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 50 96 2 8 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 50 96 (Polychromatic418967fa.accept_17_15_16_11_1_4001
  15 50 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 50 96 2 7 25 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 50 96 (accept_3_4 13 50
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50 96 2 6 25 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 50 96
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 50 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 50 96 2 5 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 50 96 (Polychromatic418967fa.accept_18_9_14_6_1_1790 9 50 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 96 2 4 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 96 (accept_3_4 7 50 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 50 96 2 3 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 50 96 (Polychromatic418967fa.accept_17_5_16_11_1_3998 5 50 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 50 96 2 2 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 50 96 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 50
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 50 96 2 1 25 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 50 96 (accept_3_4 1 50
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 96))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  48 49 96 (Eq.refl Bool.true) (allA_succ_of_accept 47 49 96 (accept_3_5 47 49 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 49 96 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 49 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 96 (Polychromatic418967fa.accept_10_5_9_6_1_697 45
  49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 96 (accept_3_5 44 49 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 96 (Polychromatic418967fa.accept_9_7_4_6_1_273 43
  49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 49 96
  (Polychromatic418967fa.accept_23_19_3_4_1_4037 42 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 49 96 (accept_3_5 41 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 49
  96 (Polychromatic418967fa.accept_15_10_4_6_1_2129 40 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 49 96 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 49 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 96 (accept_3_5 38 49 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 96 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 49 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 96
  (Polychromatic418967fa.accept_11_3_5_8_1_458 36 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 49 96 (accept_3_5 35 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 49
  96 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 49 96 (Polychromatic418967fa.accept_10_3_9_6_1_94 33 49 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 96 (accept_3_5 32 49 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 49 96 (Polychromatic418967fa.accept_19_12_11_1_1_4036 31 49 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 96 (Polychromatic418967fa.accept_9_3_4_6_1_252 30
  49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 96 (accept_3_5 29 49 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 96 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 49
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 96
  (Polychromatic418967fa.accept_18_9_13_6_1_877 27 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 96 (accept_3_5 26 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 49
  96 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 49 96 (Polychromatic418967fa.accept_11_2_5_8_1_470 24 49 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 96 (accept_3_5 23 49 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 49 96 (Polychromatic418967fa.accept_17_5_15_11_1_3978 22 49 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 96 (Polychromatic418967fa.accept_9_3_4_6_1_252 21
  49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 96 (accept_3_5 20 49 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 96 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 49
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 96
  (Polychromatic418967fa.accept_19_18_11_1_1_4035 18 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 96 (accept_3_5 17 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 49
  96 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 49 96 (Polychromatic418967fa.accept_10_5_9_6_1_697 15 49 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 96 (accept_3_5 14 49 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 49 96 (Polychromatic418967fa.accept_10_3_9_6_1_94 13 49 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 96 (Polychromatic418967fa.accept_9_3_4_6_1_252 12
  49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 96 (accept_3_5 11 49 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 96 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 49
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 96
  (Polychromatic418967fa.accept_14_9_7_12_1_4034 9 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 96 (accept_3_5 8 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 96
  (Polychromatic418967fa.accept_9_7_4_6_1_273 7 49 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 49 96 (Polychromatic418967fa.accept_13_6_10_5_1_1648 6 49 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 96 (accept_3_5 5 49 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 49 96 (Polychromatic418967fa.accept_13_4_10_5_1_1644 4 49 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 96 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 49
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 96 (accept_3_5 2 49 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 96 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 49
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49
  96)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 96 (allA_succ_of_accept 47 48 96
  (Polychromatic418967fa.accept_9_2_3_6_1_88 47 48 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 48 96 2 23 24 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 48 96 3 15 16 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 44 48 96 4 11 12 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 48 96 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 48 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 96 6 7 8 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 96 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 48 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 96 8 5 6 12 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 48 96 3 13 16 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 48 96 2 19 24 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 96
  (Polychromatic418967fa.accept_9_1_3_6_1_70 37 48 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 48 96 12 3 4 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 48 96 (Polychromatic418967fa.accept_9_8_3_6_1_533 35 48 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48 96 2 17 24 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 48 96 3 11 16 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 48 96 16 2 3 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 48 96 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 48 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 96 6 5 8 16 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 96
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 48 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 48 96 4 7 12 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 48 96 3 9 16 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 48 96 2 13 24 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 48 96 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 48 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 96 24 1 2 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 96 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 48 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 96 2 11 24 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 48 96 3 7 16 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 48 96 4 5 12 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 48 96
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 48 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 48 96 6 3 8 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 48 96 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 48 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48 96 16 1 3 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 48 96 3 5 16 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 48 96 2 7 24 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 96 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 48 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 96 12 1 4 8 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 96
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 48 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 48 96 2 5 24 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 48 96 3 3 16 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 48 96 8 1 6 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 48 96 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 48 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 96 6 1 8 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 96 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 48 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 96 4 1 12 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 48 96 3 1 16 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 48 96 2 1 24 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 96
  (Polychromatic418967fa.accept_7_1_6_5_1_39 1 48 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 48 96)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 96 (allA_succ_of_accept 46 47 96
  (accept_3_4 46 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 96
  (Polychromatic418967fa.accept_14_3_5_12_1_4000 45 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 96 (Polychromatic418967fa.accept_9_8_2_6_1_875 44 47 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 96 (accept_3_4 43 47 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 96 (Polychromatic418967fa.accept_13_3_8_5_1_974 42 47 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 96 (Polychromatic418967fa.accept_9_5_2_6_1_265 41
  47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 96 (accept_3_4 40 47 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 96 (Polychromatic418967fa.accept_9_3_2_6_1_264 39
  47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 47 96
  (Polychromatic418967fa.accept_11_5_3_8_1_454 38 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 47 96 (accept_3_4 37 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 47
  96 (Polychromatic418967fa.accept_13_10_8_5_1_1616 36 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 47 96 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 47 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 96 (accept_3_4 34 47 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 96 (Polychromatic418967fa.accept_10_3_7_6_1_659 33 47 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 47 96
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 47 96 (accept_3_4 31 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 47
  96 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 47 96 (Polychromatic418967fa.accept_13_3_8_5_1_974 29 47 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 96 (accept_3_4 28 47 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 47 96 (Polychromatic418967fa.accept_11_5_3_8_1_454 27 47 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 47 96 (Polychromatic418967fa.accept_9_8_2_6_1_875 26
  47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 96 (accept_3_4 25 47 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 96 (Polychromatic418967fa.accept_14_10_5_12_1_3995
  24 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 96
  (Polychromatic418967fa.accept_9_5_2_6_1_265 23 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 96 (accept_3_4 22 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 47
  96 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 47 96 (Polychromatic418967fa.accept_22_20_3_8_1_4033 20 47 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 96 (accept_3_4 19 47 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 47 96 (Polychromatic418967fa.accept_21_18_5_12_1_4032 18 47 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 96 (Polychromatic418967fa.accept_9_8_2_6_1_875 17
  47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 96 (accept_3_4 16 47 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 96
  (Polychromatic418967fa.accept_17_15_13_11_1_4031 15 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 47 96 (Polychromatic418967fa.accept_9_5_2_6_1_265 14 47 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 96 (accept_3_4 13 47 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 47 96 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 47 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 96 (Polychromatic418967fa.accept_10_1_7_6_1_91 11
  47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 96 (accept_3_4 10 47 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 47 96 (Polychromatic418967fa.accept_20_9_7_16_1_4030 9
  47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 96
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 47 96 (accept_3_4 7 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 96
  (Polychromatic418967fa.accept_11_6_3_8_1_843 6 47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 47 96 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 47 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 96 (accept_3_4 4 47 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 47 96 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 47 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 96 (Polychromatic418967fa.accept_19_2_9_1_1_4029 2
  47 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 96 (accept_3_4 1 47 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47 96))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46
  96 (allA_succ_of_accept 45 46 96 (Polychromatic418967fa.accept_19_7_8_1_1_4028 45 46 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 46 96 2 22 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 46 96 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 46 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 46 96 2 21 23 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 46 96 (accept_3_5 41 46 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 46 96 2 20 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 46 96 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 46
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 46 96 2 19 23 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 46 96
  (Polychromatic418967fa.accept_7_2_4_5_1_313 37 46 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 46 96 2 18 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 46 96 (accept_3_5 35 46 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 46 96
  2 17 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 46
  96 (Polychromatic418967fa.accept_15_3_1_6_1_206 33 46 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 46 96 2 16 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 46 96 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 46 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 46 96 2 15 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 46 96 (accept_3_5 29 46 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 46 96 2 14 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 46 96 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 46 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 46 96 2 13 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 46 96 (Polychromatic418967fa.accept_9_7_1_6_1_261 25
  46 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 46 96 2 12 23 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 46 96 (accept_3_5 23 46
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 46 96 2 11 23 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 46 96
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 46 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 46 96 2 10 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 46 96 (Polychromatic418967fa.accept_21_19_4_12_1_4027 19 46 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 46 96 2 9 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 46 96 (accept_3_5 17 46 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 46 96 2 8 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 46 96 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 46 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 46 96 2 7 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 46 96 (Polychromatic418967fa.accept_7_6_4_5_1_314 13
  46 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 96 2 6 23 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 96 (accept_3_5 11 46
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46 96 2 5 23 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 46 96
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 46 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 46 96 2 4 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 46 96 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 46 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 46 96 2 3 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 46 96 (accept_3_5 5 46 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 46 96 2 2 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 46 96 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 46 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 46 96 2 1 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 46 96 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 46
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  96)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 96 (allA_succ_of_accept 44 45 96
  (Polychromatic418967fa.accept_7_2_3_5_1_34 44 45 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 96 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 45 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 45 96 3 14 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 45 96 (Polychromatic418967fa.accept_10_1_5_6_1_649 41 45 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 96
  (Polychromatic418967fa.accept_13_1_6_5_1_1610 40 45 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 45 96 3 13 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 45 96 (Polychromatic418967fa.accept_13_12_6_5_1_2335 38 45 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 96 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 45 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 45 96 3 12 15 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 45 96
  (Polychromatic418967fa.accept_20_15_5_16_1_4026 35 45 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 45 96 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 45 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 45 96 3 11 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 45 96 (Polychromatic418967fa.accept_18_14_9_6_1_1777 32 45 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 96
  (Polychromatic418967fa.accept_10_1_5_6_1_649 31 45 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 45 96 3 10 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 45 96 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 45 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 96 (Polychromatic418967fa.accept_21_7_3_12_1_1455 28 45 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 45 96 3 9 15 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 45 96
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 26 45 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 96 (Polychromatic418967fa.accept_13_12_6_5_1_2335 25 45 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 45 96 3 8 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 96 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 45 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 96
  (Polychromatic418967fa.accept_7_1_3_5_1_33 22 45 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 45 96 3 7 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 45 96 (Polychromatic418967fa.accept_18_2_9_6_1_4025 20 45 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 96 (Polychromatic418967fa.accept_10_9_5_6_1_691 19 45 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 45 96 3 6 15 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 45 96
  (Polychromatic418967fa.accept_13_4_6_5_1_2333 17 45 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 45 96 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 45 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 96 3 5 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 96 (Polychromatic418967fa.accept_10_4_5_6_1_651 14 45 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 96
  (Polychromatic418967fa.accept_18_13_9_6_1_4024 13 45 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 45 96 3 4 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 45 96 (Polychromatic418967fa.accept_10_1_5_6_1_649 11 45 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 96 (Polychromatic418967fa.accept_13_10_6_5_1_2297 10 45 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 45 96 3 3 15 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 45 96
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 45 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 96 (Polychromatic418967fa.accept_18_7_9_6_1_4023 7 45 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 96 3 2 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 45 96 (Polychromatic418967fa.accept_14_5_3_12_1_324 5 45 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 96
  (Polychromatic418967fa.accept_10_4_5_6_1_651 4 45 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 45 96 3 1 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 45 96 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 45 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 96 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 45 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  96))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 96 (allA_succ_of_accept 43 44 96 (accept_3_4 43 44 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 44 96 2 21 22 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 44 96 (Polychromatic418967fa.accept_9_5_8_6_1_281 41
  44 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 44 96 4 10 11 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 44 96
  (Polychromatic418967fa.accept_7_4_2_5_1_527 39 44 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 44 96 2 19 22 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 44 96 (accept_3_4 37 44 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 96
  4 9 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44
  96 (Polychromatic418967fa.accept_10_5_4_6_1_319 35 44 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 44 96 2 17 22 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 44 96 (Polychromatic418967fa.accept_19_14_6_1_1_4022 33 44 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 44 96 4 8 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 44 96 (accept_3_4 31 44 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 44 96 2 15 22 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 44 96 (Polychromatic418967fa.accept_9_2_8_6_1_79 29 44 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 44 96 4 7 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 44 96 (Polychromatic418967fa.accept_18_9_8_6_1_4021 27
  44 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 44 96 2 13 22 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 44 96 (accept_3_4 25 44
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 44 96 4 6 11 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 44 96
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 44 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 44 96 2 11 22 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 44 96 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 44 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 44 96 4 5 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 44 96 (accept_3_4 19 44 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 44 96 2 9 22 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 44 96 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 44 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 44 96 4 4 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 44 96 (Polychromatic418967fa.accept_10_5_4_6_1_319 15
  44 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 44 96 2 7 22 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 44 96 (accept_3_4 13 44
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44 96 4 3 11 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 44 96
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 44 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 44 96 2 5 22 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 44 96 (Polychromatic418967fa.accept_15_9_14_6_1_3004 9 44 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 44 96 4 2 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 44 96 (accept_3_4 7 44 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 44 96 2 3 22 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 44 96 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 44 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 44 96 4 1 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 44 96 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 44
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 44 96 2 1 22 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 44 96 (accept_3_4 1 44
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 96)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43
  96 (allA_succ_of_accept 42 43 96 (Polychromatic418967fa.accept_11_9_10_8_1_444 42 43 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 43 96 (accept_3_5 41 43 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 43 96 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 43 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 96 (Polychromatic418967fa.accept_7_4_1_5_1_540 39
  43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 96 (accept_3_5 38 43 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 96 (Polychromatic418967fa.accept_9_1_7_6_1_75 37
  43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 96
  (Polychromatic418967fa.accept_13_10_4_5_1_2331 36 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 96 (accept_3_5 35 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 43
  96 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 43 96 (Polychromatic418967fa.accept_20_13_3_16_1_4020 33 43 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 96 (accept_3_5 32 43 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 43 96 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 43 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 96 (Polychromatic418967fa.accept_9_3_7_6_1_76 30
  43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 96 (accept_3_5 29 43 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 43 96 (Polychromatic418967fa.accept_9_1_7_6_1_75 28
  43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 96
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 43 96 (accept_3_5 26 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 43
  96 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 43 96 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 43 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 43 96 (accept_3_5 23 43 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 43 96 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 43 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 96 (Polychromatic418967fa.accept_9_3_7_6_1_76 21
  43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 96 (accept_3_5 20 43 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 96 (Polychromatic418967fa.accept_9_1_7_6_1_75 19
  43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 96
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 96 (accept_3_5 17 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 43
  96 (Polychromatic418967fa.accept_19_16_5_1_1_4019 16 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 96 (Polychromatic418967fa.accept_13_2_4_5_1_3152 15 43 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 96 (accept_3_5 14 43 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 96 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 43 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 96
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 96 (accept_3_5 11 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 43
  96 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 43 96 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 43 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 96 (accept_3_5 8 43 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 43 96 (Polychromatic418967fa.accept_10_7_3_6_1_644 7 43 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 96 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 43
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 43 96 (accept_3_5 5 43 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43 96 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 43
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 43 96
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 43 96 (accept_3_5 2 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 96
  (Polychromatic418967fa.accept_9_1_7_6_1_75 1 43 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 43 96))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 96 (allA_succ_of_accept 41 42 96
  (Polychromatic418967fa.accept_10_1_2_6_1_638 41 42 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 42 96 2 20 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 42 96 3 13 14 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 38 42 96 2 19 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 42 96 (Polychromatic418967fa.accept_13_11_3_5_1_982 37 42 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 96 6 6 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 96 (Polychromatic418967fa.accept_13_9_3_5_1_1605 35 42 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 96 2 17 21 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 42 96 3 11 14 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 42 96 2 16 21 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 42 96
  (Polychromatic418967fa.accept_10_1_2_6_1_638 31 42 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 42 96 6 5 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 42 96 (Polychromatic418967fa.accept_19_10_4_1_1_4018 29 42 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 96 2 14 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 42 96 3 9 14 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 42 96 2 13 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 96 (Polychromatic418967fa.accept_15_10_12_6_1_3000 25 42 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 96 6 4 7 16 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 96
  (Polychromatic418967fa.accept_22_1_20_8_1_4017 23 42 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 42 96 2 11 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 42 96 3 7 14 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 42 96 2 10 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 42 96 (Polychromatic418967fa.accept_13_6_3_5_1_3167 19 42 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 96 6 3 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 96 (Polychromatic418967fa.accept_15_2_12_6_1_3063 17 42 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42 96 2 8 21 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 42 96 3 5 14 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 42 96 2 7 21 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 96
  (Polychromatic418967fa.accept_25_13_17_21_1_4016 13 42 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 42 96 6 2 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 42 96 (Polychromatic418967fa.accept_10_1_2_6_1_638 11 42 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 96 2 5 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 42 96 3 3 14 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 42 96 2 4 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 42 96 (Polychromatic418967fa.accept_15_7_12_6_1_1327 7 42 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 96 6 1 7 16 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 96
  (Polychromatic418967fa.accept_15_5_12_6_1_639 5 42 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 42 96 2 2 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 42 96 3 1 14 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 42 96 2 1 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 42 96 (Polychromatic418967fa.accept_10_1_2_6_1_638 1 42 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 42 96)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 96
  (allA_succ_of_accept 40 41 96 (accept_3_4 40 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41
  96 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 96 (Polychromatic418967fa.accept_9_2_5_6_1_536 38 41 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 96 (accept_3_4 37 41 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 96 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 41 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 96 (Polychromatic418967fa.accept_9_8_5_6_1_538 35
  41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 96 (accept_3_4 34 41 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 96 (Polychromatic418967fa.accept_13_7_2_5_1_2344
  33 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 96
  (Polychromatic418967fa.accept_7_4_6_5_1_141 32 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 96 (accept_3_4 31 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 41
  96 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 41 96 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 41 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 96 (accept_3_4 28 41 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 41 96 (Polychromatic418967fa.accept_10_7_1_6_1_673 27 41 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 96 (Polychromatic418967fa.accept_9_8_5_6_1_538 26
  41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 96 (accept_3_4 25 41 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 96 (Polychromatic418967fa.accept_15_9_11_6_1_637
  24 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 96
  (Polychromatic418967fa.accept_13_10_2_5_1_1633 23 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 96 (accept_3_4 22 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 41
  96 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 41 96 (Polychromatic418967fa.accept_9_2_5_6_1_536 20 41 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 96 (accept_3_4 19 41 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 41 96 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 41 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 96 (Polychromatic418967fa.accept_9_8_5_6_1_538 17
  41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 96 (accept_3_4 16 41 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 96 (Polychromatic418967fa.accept_7_1_6_5_1_39 15
  41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 96
  (Polychromatic418967fa.accept_23_14_18_4_1_4015 14 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 96 (accept_3_4 13 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 41
  96 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 41 96 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 41 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 96 (accept_3_4 10 41 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 41 96 (Polychromatic418967fa.accept_13_9_2_5_1_2310 9 41 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 96 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 41
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 96 (accept_3_4 7 41 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 96 (Polychromatic418967fa.accept_14_6_13_12_1_810 6
  41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 96
  (Polychromatic418967fa.accept_10_5_1_6_1_672 5 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 96 (accept_3_4 4 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41 96
  (Polychromatic418967fa.accept_9_3_5_6_1_253 3 41 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 96 (Polychromatic418967fa.accept_9_2_5_6_1_536 2 41 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 96 (accept_3_4 1 41 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 96))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 96 (allA_succ_of_accept 39 40 96
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 40 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 40 96 2 19 20 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 40 96 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 40 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 40 96 4 9 10 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 40 96 (accept_3_5 35 40 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 40 96 2 17 20 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 40 96 (Polychromatic418967fa.accept_15_3_10_6_1_632 33 40 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 40 96 8 4 5 12 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 40 96 (Polychromatic418967fa.accept_15_1_10_6_1_631 31
  40 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 40 96 2 15 20 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 40 96 (accept_3_5 29 40
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 40 96 4 7 10 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 40 96
  (Polychromatic418967fa.accept_15_12_10_6_1_2134 27 40 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 40 96 2 13 20 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 40 96 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 40 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 40 96 8 3 5 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 40 96 (accept_3_5 23 40 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 40 96 2 11 20 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 40 96 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 40 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 40 96 4 5 10 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 40 96 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 40
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 40 96 2 9 20 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 40 96 (accept_3_5 17 40
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 40 96 8 2 5 12 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 40 96
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 15 40 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 40 96 2 7 20 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 40 96 (Polychromatic418967fa.accept_17_13_6_11_1_4014 13 40 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 40 96 4 3 10 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 40 96 (accept_3_5 11 40 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 40 96 2 5 20 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 40 96 (Polychromatic418967fa.accept_13_9_1_5_1_964 9 40 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 40 96 8 1 5 12 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 40 96 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 40
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 40 96 2 3 20 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 40 96 (accept_3_5 5 40
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 40 96 4 1 10 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 40 96
  (Polychromatic418967fa.accept_9_3_4_6_1_252 3 40 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 40 96 2 1 20 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 40 96 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 40 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 40 96)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 96 (allA_succ_of_accept 38
  39 96 (Polychromatic418967fa.accept_9_2_3_6_1_88 38 39 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 96 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 39 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 96 3 12 13 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 96 (Polychromatic418967fa.accept_9_8_3_6_1_533 35 39 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 96
  (Polychromatic418967fa.accept_7_6_4_5_1_314 34 39 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 39 96 3 11 13 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 39 96 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 39 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 96 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 39 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 96 3 10 13 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 96
  (Polychromatic418967fa.accept_7_1_4_5_1_35 29 39 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 96 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 39 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 96 3 9 13 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 96 (Polychromatic418967fa.accept_9_8_3_6_1_533 26 39 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 96
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 39 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 39 96 3 8 13 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 39 96 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 39 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 96 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 39 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 96 3 7 13 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 96
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 39 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 96 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 39 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 96 3 6 13 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 96 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 39 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 96
  (Polychromatic418967fa.accept_7_2_4_5_1_313 16 39 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 39 96 3 5 13 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 39 96 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 39 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 96 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 39 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 39 96 3 4 13 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 39 96
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 39 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 96 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 39 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 96 3 3 13 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 96 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 39 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 96
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 39 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 39 96 3 2 13 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 39 96 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 39 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 96 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 39 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 39 96 3 1 13 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 39 96
  (Polychromatic418967fa.accept_7_2_4_5_1_313 2 39 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 96 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 39 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 39 96))))))))))))))))))))))))))))))))))))))) (allB_succ 38 96
  (allA_succ_of_accept 37 38 96 (accept_3_4 37 38 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38 96
  2 18 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 38
  96 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 38 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 38 96 2 17 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 38 96 (Polychromatic418967fa.accept_10_3_8_6_1_326 33 38 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 96 2 16 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 96 (accept_3_4 31 38 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 38 96 2 15 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 38 96 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 38 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 38 96 2 14 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 38 96 (Polychromatic418967fa.accept_13_1_12_5_1_1601
  27 38 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 96 2 13 19 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 96 (accept_3_4 25 38
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 96 2 12 19 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 96
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 38 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 38 96 2 11 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 38 96 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 38 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 38 96 2 10 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 38 96 (accept_3_4 19 38 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 38 96 2 9 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 38 96 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 38 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 38 96 2 8 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 38 96 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 38
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 96 2 7 19 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 96 (accept_3_4 13 38
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 96 2 6 19 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 38 96
  (Polychromatic418967fa.accept_20_11_18_16_1_1559 11 38 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 38 96 2 5 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 38 96 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 38 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 38 96 2 4 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 38 96 (accept_3_4 7 38 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 38 96 2 3 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 38 96 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 38 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 38 96 2 2 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 38 96 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 38
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 96 2 1 19 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 96 (accept_3_4 1 38
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 96)))))))))))))))))))))))))))))))))))))) (allB_succ 37 96
  (allA_succ_of_accept 36 37 96 (Polychromatic418967fa.accept_17_2_3_11_1_2919 36 37 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 96 (accept_3_5 35 37 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 37 96 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 37 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 96 (Polychromatic418967fa.accept_10_3_7_6_1_659 33
  37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 96 (accept_3_5 32 37 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 96 (Polychromatic418967fa.accept_7_3_2_5_1_147 31
  37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 96
  (Polychromatic418967fa.accept_9_3_1_6_1_86 30 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 96 (accept_3_5 29 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 37
  96 (Polychromatic418967fa.accept_15_13_7_6_1_682 28 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 37 96 (Polychromatic418967fa.accept_15_12_7_6_1_4013 27 37 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 96 (accept_3_5 26 37 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 37 96 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 37 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 96 (Polychromatic418967fa.accept_7_3_2_5_1_147 24
  37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 96 (accept_3_5 23 37 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 37 96 (Polychromatic418967fa.accept_9_4_1_6_1_284 22
  37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 96
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 37 96 (accept_3_5 20 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 37
  96 (Polychromatic418967fa.accept_13_6_11_5_1_133 19 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 37 96 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 37 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 96 (accept_3_5 17 37 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 37 96 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 37 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 96 (Polychromatic418967fa.accept_30_15_7_6_1_4012
  15 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 96 (accept_3_5 14 37
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 96 (Polychromatic418967fa.accept_9_4_1_6_1_284
  13 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 96
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 96 (accept_3_5 11 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 37
  96 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 37 96 (Polychromatic418967fa.accept_17_9_3_11_1_3983 9 37 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 96 (accept_3_5 8 37 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 37 96 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 37 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 96 (Polychromatic418967fa.accept_13_6_11_5_1_133 6
  37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 96 (accept_3_5 5 37 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37 96 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 37
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 96
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 37 96 (accept_3_5 2 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37 96
  (Polychromatic418967fa.accept_10_1_7_6_1_91 1 37 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 37 96))))))))))))))))))))))))))))))))))))) (allB_succ 36 96 (allA_succ_of_accept 35 36 96
  (Polychromatic418967fa.accept_19_16_17_1_1_4011 35 36 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 36 96 2 17 18 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 36 96 3 11 12 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 36 96 4 8 9 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 36 96 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 36 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 96 6 5 6 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 96 (Polychromatic418967fa.accept_19_10_17_1_1_4010 29 36 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 96 4 7 9 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 36 96 3 9 12 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 36 96 2 13 18 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 36 96
  (Polychromatic418967fa.accept_7_4_1_5_1_540 25 36 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 36 96 12 2 3 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 36 96 (Polychromatic418967fa.accept_19_4_17_1_1_4009 23 36 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 96 2 11 18 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 36 96 3 7 12 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 36 96 4 5 9 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 96 (Polychromatic418967fa.accept_13_6_10_5_1_1648 19 36 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 96 6 3 6 16 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 96
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 36 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 36 96 4 4 9 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 36 96 3 5 12 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 36 96 2 7 18 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 36 96 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 36 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 96 12 1 3 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 96 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 36 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36 96 2 5 18 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 36 96 3 3 12 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 36 96 4 2 9 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 96
  (Polychromatic418967fa.accept_21_7_15_12_1_4008 7 36 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 36 96 6 1 6 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 36 96 (Polychromatic418967fa.accept_11_5_3_8_1_454 5 36 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 96 4 1 9 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 36 96 3 1 12 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 36 96 2 1 18 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 96 (Polychromatic418967fa.accept_21_1_15_12_1_4007 1 36 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 96))))))))))))))))))))))))))))))))))))
  (allB_succ 35 96 (allA_succ_of_accept 34 35 96 (accept_3_4 34 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 35 96 (Polychromatic418967fa.accept_14_5_7_12_1_4006 33 35 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 35 96 (Polychromatic418967fa.accept_9_5_8_6_1_281 32 35 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 96 (accept_3_4 31 35 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 35 96 (Polychromatic418967fa.accept_9_3_8_6_1_80 30
  35 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 96
  (Polychromatic418967fa.accept_9_2_8_6_1_79 29 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 35 96 (accept_3_4 28 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35
  96 (Polychromatic418967fa.accept_11_5_2_8_1_866 27 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 35 96 (Polychromatic418967fa.accept_15_11_5_6_1_669 26 35 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 96 (accept_3_4 25 35 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 35 96 (Polychromatic418967fa.accept_10_4_5_6_1_651 24 35 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 96 (Polychromatic418967fa.accept_9_5_8_6_1_281 23
  35 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 96 (accept_3_4 22 35 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 96 (Polychromatic418967fa.accept_9_3_8_6_1_80 21
  35 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 35 96
  (Polychromatic418967fa.accept_9_2_8_6_1_79 20 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 35 96 (accept_3_4 19 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 35
  96 (Polychromatic418967fa.accept_15_3_5_6_1_4005 18 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 35 96 (Polychromatic418967fa.accept_13_4_9_5_1_1641 17 35 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 96 (accept_3_4 16 35 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 35 96 (Polychromatic418967fa.accept_13_2_9_5_1_959 15 35 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 35 96 (Polychromatic418967fa.accept_9_5_8_6_1_281 14
  35 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 96 (accept_3_4 13 35 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 96 (Polychromatic418967fa.accept_9_3_8_6_1_80 12
  35 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 96
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 35 96 (accept_3_4 10 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 35
  96 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 35 96 (Polychromatic418967fa.accept_17_8_1_11_1_4004 8 35 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 96 (accept_3_4 7 35 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 35 96 (Polychromatic418967fa.accept_21_6_14_12_1_4003 6 35 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 96 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 35
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 96 (accept_3_4 4 35 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 96 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 35
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 96
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 96 (accept_3_4 1 35 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  96))))))))))))))))))))))))))))))))))) (allB_succ 34 96 (allA_succ_of_accept 33 34 96
  (Polychromatic418967fa.accept_18_15_16_6_1_1751 33 34 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 34 96 2 16 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 34 96 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 34 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 34 96 2 15 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 34 96 (accept_3_5 29 34 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 34 96 2 14 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 34 96 (Polychromatic418967fa.accept_13_1_8_5_1_2315 27 34 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 34 96 2 13 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 34 96 (Polychromatic418967fa.accept_7_4_6_5_1_141 25
  34 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 34 96 2 12 17 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 34 96 (accept_3_5 23 34
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34 96 2 11 17 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 34 96
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 34 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 34 96 2 10 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 34 96 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 34 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 34 96 2 9 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 34 96 (accept_3_5 17 34 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 34 96 2 8 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 34 96 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 34 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 34 96 2 7 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 34 96 (Polychromatic418967fa.accept_9_4_7_6_1_255 13
  34 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 34 96 2 6 17 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 34 96 (accept_3_5 11 34
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34 96 2 5 17 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 34 96
  (Polychromatic418967fa.accept_15_9_4_6_1_3075 9 34 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 34 96 2 4 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 34 96 (Polychromatic418967fa.accept_22_7_12_8_1_4002 7 34 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 96 2 3 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 96 (accept_3_5 5 34 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 34 96 2 2 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 34 96 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 34 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 96 2 1 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 96 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 34
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 96))))))))))))))))))))))))))))))))))
  (allB_succ 33 96 (allA_succ_of_accept 32 33 96 (Polychromatic418967fa.accept_17_15_16_11_1_4001 32 33 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 96
  (Polychromatic418967fa.accept_14_3_5_12_1_4000 31 33 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 33 96 3 10 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 33 96 (Polychromatic418967fa.accept_10_9_3_6_1_686 29 33 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 96 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 33 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 33 96 3 9 11 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 33 96
  (Polychromatic418967fa.accept_15_11_3_6_1_1306 26 33 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 96 (Polychromatic418967fa.accept_13_12_7_5_1_3147 25 33 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 96 3 8 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 96 (Polychromatic418967fa.accept_18_5_15_6_1_3999 23 33 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 96
  (Polychromatic418967fa.accept_17_5_16_11_1_3998 22 33 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 33 96 3 7 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 33 96 (Polychromatic418967fa.accept_15_5_3_6_1_2128 20 33 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 96 (Polychromatic418967fa.accept_10_9_3_6_1_686 19 33 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 33 96 3 6 11 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 33 96
  (Polychromatic418967fa.accept_10_7_3_6_1_644 17 33 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 96 (Polychromatic418967fa.accept_15_1_3_6_1_621 16 33 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 96 3 5 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 96 (Polychromatic418967fa.accept_17_14_16_11_1_3997 14 33 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 96
  (Polychromatic418967fa.accept_19_13_14_1_1_3996 13 33 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 33 96 3 4 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 33 96 (Polychromatic418967fa.accept_13_11_7_5_1_2314 11 33 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 96 (Polychromatic418967fa.accept_14_10_5_12_1_3995 10 33 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 33 96 3 3 11 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 33 96
  (Polychromatic418967fa.accept_10_8_3_6_1_685 8 33 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 96 (Polychromatic418967fa.accept_10_7_3_6_1_644 7 33 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 96 3 2 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 96 (Polychromatic418967fa.accept_15_5_3_6_1_2128 5 33 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 96
  (Polychromatic418967fa.accept_18_4_15_6_1_3994 4 33 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 33 96 3 1 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 33 96 (Polychromatic418967fa.accept_13_2_7_5_1_3189 2 33 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 96 (Polychromatic418967fa.accept_15_1_3_6_1_621 1 33 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 96)))))))))))))))))))))))))))))))))
  (allB_succ 32 96 (allA_succ_of_accept 31 32 96 (accept_3_4 31 32 96 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 32 96 2 15 16 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 32 96 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 32 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 32 96 4 7 8 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 32 96 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 32 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 96 2 13 16 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 96 (accept_3_4 25 32 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 96 8 3 4 12 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 32 96 (Polychromatic418967fa.accept_7_2_4_5_1_313 23
  32 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 96 2 11 16 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 96
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 32 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 32 96 4 5 8 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 32 96 (accept_3_4 19 32 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32 96
  2 9 16 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 32
  96 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 32 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 32 96 16 1 2 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 32 96 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 32 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 96 2 7 16 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 96 (accept_3_4 13 32 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 32 96 4 3 8 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 32 96 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 32 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 32 96 2 5 16 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 32 96 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 32
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 32 96 8 1 4 12 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 32 96 (accept_3_4 7 32 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 96 2 3 16 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 32 96 (Polychromatic418967fa.accept_17_5_15_11_1_3978 5 32 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 32 96 4 1 8 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 32 96
  (Polychromatic418967fa.accept_9_3_5_6_1_253 3 32 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 32 96 2 1 16 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 32 96 (accept_3_4 1 32 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32
  96)))))))))))))))))))))))))))))))) (allB_succ 31 96 (allA_succ_of_accept 30 31 96
  (Polychromatic418967fa.accept_7_2_3_5_1_34 30 31 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 96 (accept_3_5 29 31 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 31
  96 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 31 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 31 96 (Polychromatic418967fa.accept_10_7_1_6_1_673 27 31 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 96 (accept_3_5 26 31 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 31 96 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 31 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 96 (Polychromatic418967fa.accept_15_9_1_6_1_657 24
  31 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 96 (accept_3_5 23 31 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 31 96 (Polychromatic418967fa.accept_7_1_3_5_1_33 22
  31 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 96
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 31 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 31 96 (accept_3_5 20 31 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31
  96 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 31 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 31 96 (Polychromatic418967fa.accept_15_3_1_6_1_206 18 31 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 96 (accept_3_5 17 31 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 31 96 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 31 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 96 (Polychromatic418967fa.accept_7_1_3_5_1_33 15
  31 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 96 (accept_3_5 14 31 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 96 (Polychromatic418967fa.accept_19_13_12_1_1_3993
  13 31 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 96
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 31 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 96 (accept_3_5 11 31 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 31
  96 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 31 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 31 96 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 31 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 96 (accept_3_5 8 31 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 31 96 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 31 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 96 (Polychromatic418967fa.accept_20_6_11_16_1_3992
  6 31 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 31 96 (accept_3_5 5 31 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31 96 (Polychromatic418967fa.accept_19_4_12_1_1_3991 4
  31 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 31 96
  (Polychromatic418967fa.accept_9_3_4_6_1_252 3 31 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 31 96 (accept_3_5 2 31 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 96
  (Polychromatic418967fa.accept_7_1_3_5_1_33 1 31 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 31 96))))))))))))))))))))))))))))))) (allB_succ 30 96 (allA_succ_of_accept 29 30 96
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 30 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 30 96 2 14 15 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 30 96 3 9 10 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 30 96 2 13 15 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 30 96 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 30 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 96 6 4 5 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 96 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 30 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 96 2 11 15 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 30 96 3 7 10 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 30 96 2 10 15 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 96
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 30 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 30 96 6 3 5 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 30 96 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 30 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 96 2 8 15 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 30 96 3 5 10 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 30 96 2 7 15 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 96 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 30 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 96 6 2 5 16 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 96
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 30 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 30 96 2 5 15 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 30 96 3 3 10 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 30 96 2 4 15 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 30 96 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 30 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 96 6 1 5 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 96 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 30 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 30 96 2 2 15 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 30 96 3 1 10 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 30 96 2 1 15 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 96
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 30 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 30 96)))))))))))))))))))))))))))))) (allB_succ 29 96 (allA_succ_of_accept 28 29 96 (accept_3_4 28 29 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 96 (Polychromatic418967fa.accept_7_6_1_5_1_322 27
  29 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 96
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 29 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 29 96 (accept_3_4 25 29 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 29
  96 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 29 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 29 96 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 29 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 96 (accept_3_4 22 29 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 29 96 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 29 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 96 (Polychromatic418967fa.accept_7_6_1_5_1_322 20
  29 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 96 (accept_3_4 19 29 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 96 (Polychromatic418967fa.accept_7_4_1_5_1_540 18
  29 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 96
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 29 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 96 (accept_3_4 16 29 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 29
  96 (Polychromatic418967fa.accept_10_5_9_6_1_697 15 29 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 29 96 (Polychromatic418967fa.accept_9_5_2_6_1_265 14 29 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 96 (accept_3_4 13 29 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 29 96 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 29 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 96 (Polychromatic418967fa.accept_7_4_1_5_1_540 11
  29 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 96 (accept_3_4 10 29 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 96 (Polychromatic418967fa.accept_13_9_3_5_1_1605 9
  29 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 96
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 29 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 29 96 (accept_3_4 7 29 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 96
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 29 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 29 96 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 29 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 96 (accept_3_4 4 29 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 29 96 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 29 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 96 (Polychromatic418967fa.accept_13_2_3_5_1_2294 2
  29 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 96 (accept_3_4 1 29 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29 96))))))))))))))))))))))))))))) (allB_succ 28 96
  (allA_succ_of_accept 27 28 96 (Polychromatic418967fa.accept_19_8_9_1_1_3990 27 28 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 28 96 2 13 14 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 28 96 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 28 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 96 4 6 7 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 96 (accept_3_5 23 28 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 28 96 2 11 14 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 28 96 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 28
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 28 96 4 5 7 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 28 96
  (Polychromatic418967fa.accept_15_4_13_6_1_642 19 28 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 28 96 2 9 14 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 28 96 (accept_3_5 17 28 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 28 96
  4 4 7 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 28 96
  (Polychromatic418967fa.accept_18_15_10_6_1_1781 15 28 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 28 96 2 7 14 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 28 96 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 28 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 28 96 4 3 7 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 28 96 (accept_3_5 11 28 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 28 96 2 5 14 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 28 96 (Polychromatic418967fa.accept_13_9_2_5_1_2310 9 28 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 28 96 4 2 7 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 28 96 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 28
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 28 96 2 3 14 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 28 96 (accept_3_5 5 28
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 28 96 4 1 7 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 28 96 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 28
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 28 96 2 1 14 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 28 96
  (Polychromatic418967fa.accept_21_1_7_12_1_1465 1 28 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 28 96)))))))))))))))))))))))))))) (allB_succ 27 96 (allA_succ_of_accept 26 27 96
  (Polychromatic418967fa.accept_18_8_9_6_1_3989 26 27 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 96 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 27 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 27 96 3 8 9 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 27 96 (Polychromatic418967fa.accept_10_3_7_6_1_659 23 27 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 96
  (Polychromatic418967fa.accept_7_1_6_5_1_39 22 27 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 27 96 3 7 9 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 27 96 (Polychromatic418967fa.accept_14_6_13_12_1_810 20 27 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 96 (Polychromatic418967fa.accept_13_6_1_5_1_3988 19 27 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 27 96 3 6 9 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 27 96
  (Polychromatic418967fa.accept_13_4_1_5_1_1628 17 27 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 27 96 (Polychromatic418967fa.accept_13_3_1_5_1_499 16 27 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 27 96 3 5 9 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 27 96 (Polychromatic418967fa.accept_11_3_5_8_1_458 14 27 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 96
  (Polychromatic418967fa.accept_10_3_7_6_1_659 13 27 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 27 96 3 4 9 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 27 96 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 27 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 96 (Polychromatic418967fa.accept_15_10_12_6_1_3000 10 27 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 27 96 3 3 9 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 27 96
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 27 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 96 (Polychromatic418967fa.accept_15_7_12_6_1_1327 7 27 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 27 96 3 2 9 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 27 96 (Polychromatic418967fa.accept_15_5_12_6_1_639 5 27 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 96
  (Polychromatic418967fa.accept_7_4_6_5_1_141 4 27 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 27 96 3 1 9 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 27 96 (Polychromatic418967fa.accept_11_2_5_8_1_470 2 27 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 96 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 27 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 96))))))))))))))))))))))))))) (allB_succ 26
  96 (allA_succ_of_accept 25 26 96 (accept_3_4 25 26 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26
  96 2 12 13 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  26 96 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 26 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 26 96 2 11 13 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 26 96 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 26 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 96 2 10 13 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 96 (accept_3_4 19 26 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 96 2 9 13 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 26 96 (Polychromatic418967fa.accept_15_2_11_6_1_2135 17 26 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 26 96 2 8 13 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 26 96
  (Polychromatic418967fa.accept_21_15_5_12_1_3987 15 26 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 26 96 2 7 13 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 26 96 (accept_3_4 13 26 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26 96
  2 6 13 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 26
  96 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 26 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 26 96 2 5 13 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 26 96 (Polychromatic418967fa.accept_15_9_11_6_1_637 9 26 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 26 96 2 4 13 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 26 96 (accept_3_4 7 26 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 26 96 2 3 13 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 26 96 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 26 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 26 96 2 2 13 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 26 96 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 26
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 26 96 2 1 13 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 26 96 (accept_3_4 1 26
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26 96)))))))))))))))))))))))))) (allB_succ 25 96
  (allA_succ_of_accept 24 25 96 (Polychromatic418967fa.accept_10_4_5_6_1_651 24 25 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 96 (accept_3_5 23 25 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 25 96 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 25 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 96 (Polychromatic418967fa.accept_9_3_7_6_1_76 21
  25 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 96 (accept_3_5 20 25 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 96 (Polychromatic418967fa.accept_9_1_7_6_1_75 19
  25 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 96
  (Polychromatic418967fa.accept_15_3_10_6_1_632 18 25 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 96 (accept_3_5 17 25 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 25
  96 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 25 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 25 96 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 25 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 96 (accept_3_5 14 25 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 25 96 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 25 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 96 (Polychromatic418967fa.accept_9_3_7_6_1_76 12
  25 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 96 (accept_3_5 11 25 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 25 96 (Polychromatic418967fa.accept_9_1_7_6_1_75 10
  25 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 25 96
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 25 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 25 96 (accept_3_5 8 25 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 96
  (Polychromatic418967fa.accept_13_7_12_5_1_1603 7 25 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 25 96 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 25 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 25 96 (accept_3_5 5 25 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 25 96 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 25 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 96 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 25
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 96 (accept_3_5 2 25 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 96 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 25
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 96))))))))))))))))))))))))) (allB_succ 24
  96 (allA_succ_of_accept 23 24 96 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 24 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 96 2 11 12 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 24 96 3 7 8 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 24 96 4 5 6 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 24 96 (Polychromatic418967fa.accept_13_6_11_5_1_133 19 24 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 96 6 3 4 16 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 96
  (Polychromatic418967fa.accept_21_17_3_12_1_3986 17 24 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 24 96 8 2 3 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 24 96 3 5 8 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 24 96 2 7 12 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 24 96 (Polychromatic418967fa.accept_17_13_7_11_1_3985 13 24 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 96 12 1 2 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 96 (Polychromatic418967fa.accept_15_11_9_6_1_1321 11 24 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 96 2 5 12 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 24 96 3 3 8 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 24 96 8 1 3 12 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 24 96
  (Polychromatic418967fa.accept_13_7_11_5_1_2302 7 24 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 24 96 6 1 4 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 24 96 (Polychromatic418967fa.accept_10_5_4_6_1_319 5 24 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 96 4 1 6 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 24 96 3 1 8 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 24 96 2 1 12 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 96 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 24 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 96)))))))))))))))))))))))) (allB_succ 23 96
  (allA_succ_of_accept 22 23 96 (accept_3_4 22 23 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23
  96 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 23 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 96 (Polychromatic418967fa.accept_9_2_5_6_1_536 20 23 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 96 (accept_3_4 19 23 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 96 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 23 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 96 (Polychromatic418967fa.accept_7_3_2_5_1_147 17
  23 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 96 (accept_3_4 16 23 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 96 (Polychromatic418967fa.accept_11_4_1_8_1_1366
  15 23 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 96
  (Polychromatic418967fa.accept_15_14_8_6_1_2133 14 23 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 96 (accept_3_4 13 23 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 23
  96 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 23 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 23 96 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 23 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 96 (accept_3_4 10 23 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 23 96 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 23 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 96 (Polychromatic418967fa.accept_9_8_5_6_1_538 8 23
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 96 (accept_3_4 7 23 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 96 (Polychromatic418967fa.accept_13_6_10_5_1_1648 6
  23 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 96
  (Polychromatic418967fa.accept_17_5_6_11_1_3974 5 23 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 96 (accept_3_4 4 23 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23 96
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 23 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 23 96 (Polychromatic418967fa.accept_9_2_5_6_1_536 2 23 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 96 (accept_3_4 1 23 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 23 96))))))))))))))))))))))) (allB_succ 22 96 (allA_succ_of_accept 21 22 96
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 22 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 22 96 2 10 11 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 22 96 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 22 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 22 96 2 9 11 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 22 96 (accept_3_5 17 22 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 22 96 2 8 11 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 22 96 (Polychromatic418967fa.accept_13_2_9_5_1_959 15 22 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 22 96 2 7 11 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 22 96 (Polychromatic418967fa.accept_7_6_1_5_1_322 13
  22 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 22 96 2 6 11 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 22 96 (accept_3_5 11 22
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 22 96 2 5 11 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 22 96
  (Polychromatic418967fa.accept_21_9_1_12_1_3984 9 22 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 22 96 2 4 11 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 22 96 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 22 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 22 96 2 3 11 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 22 96 (accept_3_5 5 22 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 22 96 2 2 11 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 22 96 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 22 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 22 96 2 1 11 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 22 96 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 22 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 96)))))))))))))))))))))) (allB_succ 21 96
  (allA_succ_of_accept 20 21 96 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 21 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 96 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 21 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 96 3 6 7 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 96
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 21 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 96 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 21 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 21 96 3 5 7 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 21 96 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 21 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 96
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 21 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 21 96 3 4 7 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 21 96 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 21 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 96 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 21 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 96 3 3 7 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 96
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 21 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 96 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 21 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 21 96 3 2 7 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 21 96 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 21 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 96
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 21 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 21 96 3 1 7 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 21 96 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 21 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 96 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 21 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 96))))))))))))))))))))) (allB_succ 20 96
  (allA_succ_of_accept 19 20 96 (accept_3_4 19 20 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 96
  2 9 10 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 20
  96 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 20 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 20 96 4 4 5 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 20 96 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 20 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 20 96 2 7 10 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 96 (accept_3_4 13 20 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 20 96 4 3 5 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 20 96 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 20 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 96 2 5 10 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 96 (Polychromatic418967fa.accept_17_9_3_11_1_3983 9
  20 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 20 96 4 2 5 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 20 96 (accept_3_4 7 20
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 96 2 3 10 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 20 96
  (Polychromatic418967fa.accept_9_5_2_6_1_265 5 20 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 20 96 4 1 5 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 20 96 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 20 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 96 2 1 10 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 96 (accept_3_4 1 20 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 96)))))))))))))))))))) (allB_succ 19 96 (allA_succ_of_accept 18 19 96
  (Polychromatic418967fa.accept_21_18_19_12_1_3982 18 19 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 96 (accept_3_5 17 19 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 19
  96 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 19 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 19 96 (Polychromatic418967fa.accept_10_5_9_6_1_697 15 19 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 96 (accept_3_5 14 19 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 19 96 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 19 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 96 (Polychromatic418967fa.accept_9_3_1_6_1_86 12
  19 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 19 96 (accept_3_5 11 19 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 19 96 (Polychromatic418967fa.accept_13_10_6_5_1_2297
  10 19 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 19 96
  (Polychromatic418967fa.accept_15_9_4_6_1_3075 9 19 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 19 96 (accept_3_5 8 19 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 96
  (Polychromatic418967fa.accept_9_7_1_6_1_261 7 19 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 19 96 (Polychromatic418967fa.accept_21_6_19_12_1_3981 6 19 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 19 96 (accept_3_5 5 19 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 19 96 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 19 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 19 96 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 19
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 96 (accept_3_5 2 19 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 19 96 (Polychromatic418967fa.accept_13_1_6_5_1_1610 1
  19 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 96))))))))))))))))))) (allB_succ 18 96
  (allA_succ_of_accept 17 18 96 (Polychromatic418967fa.accept_19_17_18_1_1_3980 17 18 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 96 2 8 9 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 18 96 3 5 6 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 18 96 2 7 9 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 18 96 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 18 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 96 6 2 3 16 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 96
  (Polychromatic418967fa.accept_15_11_3_6_1_1306 11 18 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 18 96 2 5 9 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 18 96 3 3 6 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 18 96 2 4 9 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 18 96 (Polychromatic418967fa.accept_17_7_1_11_1_1894 7 18 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 96 6 1 3 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 96 (Polychromatic418967fa.accept_15_5_3_6_1_2128 5 18 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 96 2 2 9 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 18 96 3 1 6 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 18 96 2 1 9 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 18 96
  (Polychromatic418967fa.accept_7_1_4_5_1_35 1 18 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 18 96)))))))))))))))))) (allB_succ 17 96 (allA_succ_of_accept 16 17 96 (accept_3_4 16 17 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 96 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 17 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 96
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 17 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 96 (accept_3_4 13 17 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 17
  96 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 17 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 17 96 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 17 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 96 (accept_3_4 10 17 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 17 96 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 17 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 96 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 17
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 96 (accept_3_4 7 17 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17 96 (Polychromatic418967fa.accept_13_6_4_5_1_2330 6
  17 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 96
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 17 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 17 96 (accept_3_4 4 17 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17 96
  (Polychromatic418967fa.accept_9_3_8_6_1_80 3 17 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 17 96 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 17 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 96 (accept_3_4 1 17 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 17 96))))))))))))))))) (allB_succ 16 96 (allA_succ_of_accept 15 16 96
  (Polychromatic418967fa.accept_13_2_3_5_1_2294 15 16 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 16 96 2 7 8 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 16 96 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 16 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 16 96 4 3 4 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 16 96 (accept_3_5 11 16 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 16 96 2 5 8 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 16 96 (Polychromatic418967fa.accept_13_9_3_5_1_1605 9 16 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 16 96 8 1 2 12 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 16 96 (Polychromatic418967fa.accept_14_7_2_12_1_1430 7
  16 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 96 2 3 8 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 96 (accept_3_5 5 16
  96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 96 4 1 4 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 16 96 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 16
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 16 96 2 1 8 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 16 96
  (Polychromatic418967fa.accept_9_1_7_6_1_75 1 16 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 16 96)))))))))))))))) (allB_succ 15 96 (allA_succ_of_accept 14 15 96
  (Polychromatic418967fa.accept_10_4_5_6_1_651 14 15 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 96 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 15 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 96 3 4 5 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 96 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 15 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 96
  (Polychromatic418967fa.accept_7_3_1_5_1_44 10 15 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 15 96 3 3 5 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 15 96 (Polychromatic418967fa.accept_19_8_15_1_1_3979 8 15 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 96 (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 15 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 15 96 3 2 5 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 15 96
  (Polychromatic418967fa.accept_17_5_15_11_1_3978 5 15 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 15 96 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 15 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 96 3 1 5 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 96 (Polychromatic418967fa.accept_19_2_15_1_1_3977 2 15 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 96
  (Polychromatic418967fa.accept_10_1_5_6_1_649 1 15 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 15 96))))))))))))))) (allB_succ 14 96 (allA_succ_of_accept 13 14 96 (accept_3_4 13 14 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 96 2 6 7 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 14 96 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 14 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 14 96 2 5 7 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 14 96
  (Polychromatic418967fa.accept_13_9_1_5_1_964 9 14 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 14 96 2 4 7 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 14 96 (accept_3_4 7 14 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 14 96 2
  3 7 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 14 96
  (Polychromatic418967fa.accept_10_5_4_6_1_319 5 14 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 14 96 2 2 7 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 14 96 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 14 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 96 2 1 7 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 96 (accept_3_4 1 14 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 96)))))))))))))) (allB_succ 13 96 (allA_succ_of_accept 12 13 96
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 13 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 96 (accept_3_5 11 13 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 13
  96 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 13 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 13 96 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 13 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 96 (accept_3_5 8 13 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 13 96 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 13 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 96 (Polychromatic418967fa.accept_14_6_13_12_1_810 6
  13 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 13 96 (accept_3_5 5 13 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13 96 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 13
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 13 96
  (Polychromatic418967fa.accept_9_3_4_6_1_252 3 13 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 13 96 (accept_3_5 2 13 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 96
  (Polychromatic418967fa.accept_7_1_6_5_1_39 1 13 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 13 96))))))))))))) (allB_succ 12 96 (allA_succ_of_accept 11 12 96 (Polychromatic418967fa.accept_9_2_3_6_1_88
  11 12 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12 96 2 5 6 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 12 96 3 3 4 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 12 96 4 2 3 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 12 96
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 12 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 12 96 6 1 2 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 12 96 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 12 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 96 4 1 3 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 12 96 3 1 4 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 12 96 2 1 6 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 96 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 12 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 96)))))))))))) (allB_succ 11 96
  (allA_succ_of_accept 10 11 96 (accept_3_4 10 11 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11
  96 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 11 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 96 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 11 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 96 (accept_3_4 7 11 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 96 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 11 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 96 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 11
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 96 (accept_3_4 4 11 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 96 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 11
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 96
  (Polychromatic418967fa.accept_7_2_4_5_1_313 2 11 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 96 (accept_3_4 1 11 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11 96)))))))))))
  (allB_succ 10 96 (allA_succ_of_accept 9 10 96 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 10 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 10 96 2 4 5 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 10 96 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 10
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 10 96 2 3 5 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 10 96 (accept_3_5 5 10 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 10 96 2 2 5 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 10 96 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 10 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 10 96 2 1 5 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 10 96
  (Polychromatic418967fa.accept_7_1_3_5_1_33 1 10 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 10 96)))))))))) (allB_succ 9 96 (allA_succ_of_accept 8 9 96 (Polychromatic418967fa.accept_17_8_9_11_1_3976 8
  9 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 96
  (Polychromatic418967fa.accept_14_7_9_12_1_3975 7 9 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 9 96 3 2 3 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 9 96 (Polychromatic418967fa.accept_10_5_9_6_1_697 5 9 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 96 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 9 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 9 96 3 1 3 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 9 96
  (Polychromatic418967fa.accept_13_2_9_5_1_959 2 9 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 96 (Polychromatic418967fa.accept_13_1_9_5_1_1598 1 9 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 9 96))))))))) (allB_succ 8 96 (allA_succ_of_accept 7 8 96 (accept_3_4 7 8 96
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 8 96 2 3 4 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 8 96 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 8 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 8 96 4 1 2 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 8 96
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 8 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 8 96 2 1 4 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 8 96 (accept_3_4 1 8 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 96))))))))
  (allB_succ 7 96 (allA_succ_of_accept 6 7 96 (Polychromatic418967fa.accept_19_6_7_1_1_2805 6 7 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 7 96 (accept_3_5 5 7 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 7 96 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 7 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 7 96 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 7 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 96 (accept_3_5 2 7 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 7 96 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 7 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 96))))))) (allB_succ 6 96 (allA_succ_of_accept 5 6 96
  (Polychromatic418967fa.accept_17_5_6_11_1_3974 5 6 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 6 96 2 2 3 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 6 96 3 1 2 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 6 96 2 1 3 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 96 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 6 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 6 96)))))) (allB_succ 5 96 (allA_succ_of_accept 4 5 96 (accept_3_4 4 5 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 96 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 5 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 96
  (Polychromatic418967fa.accept_9_2_5_6_1_536 2 5 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 96 (accept_3_4 1 5 96 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 96))))) (allB_succ
  4 96 (allA_succ_of_accept 3 4 96 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 4 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 4 96 2 1 2 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 4 96 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 4 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 4 96)))) (allB_succ 3 96 (allA_succ_of_accept 2 3 96
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 3 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 96 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 3 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 3 96))) (allB_succ 2 96 (allA_succ_of_accept 1 2 96 (accept_3_4 1 2 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 2 96)) (allB_two
  96))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


