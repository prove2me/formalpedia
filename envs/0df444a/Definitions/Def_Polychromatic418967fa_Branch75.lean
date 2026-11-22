-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch75
-- name    : Polychromatic418967fa_Branch75
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:08:55.454739+00:00
-- url     : https://prove2.me/theorems/75c2bda9-3a8f-4bc3-88b0-9bb24d1070f2
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

def Polychromatic418967fa.branch_75 : allB 75 75 :=
  allB_succ' 2 74 75 (Eq.refl Bool.true) (allA_succ_of_accept 1 74 75 (accept_3_4 1 74 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 74 75)) (allB_succ' 3 73 75 (Eq.refl Bool.true) (allA_succ_of_accept 2 73 75 (accept_3_5 2 73 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 75 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 73
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73 75))) (allB_succ' 4 72 75 (Eq.refl
  Bool.true) (allA_succ_of_gcd 3 72 75 3 1 24 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 2 72 75 (Polychromatic418967fa.accept_19_2_15_18_1_1556 2 72 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 75 (Polychromatic418967fa.accept_21_1_9_12_1_2719 1
  72 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72 75)))) (allB_succ' 5 71 75 (Eq.refl
  Bool.true) (allA_succ_of_accept 4 71 75 (accept_3_4 4 71 75 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 71 75 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 71 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 75 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 71 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 75 (accept_3_4 1 71 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 71 75))))) (allB_succ' 6 70 75 (Eq.refl Bool.true) (allA_succ_of_gcd 5 70 75
  5 1 14 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 70 75
  (Polychromatic418967fa.accept_9_4_7_3_1_43 4 70 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 70 75 (Polychromatic418967fa.accept_16_3_6_11_1_2718 3 70 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 70 75 (accept_3_5 2 70 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 70 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 70 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70 75)))))) (allB_succ' 7 69 75 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 69 75 3 2 23 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 69 75 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 69 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 75 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 69 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 69 75 3 1 23 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 75
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 69 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 69 75 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 69 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 69 75))))))) (allB_succ' 8 68 75 (Eq.refl Bool.true) (allA_succ_of_accept 7
  68 75 (accept_3_4 7 68 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68 75
  (Polychromatic418967fa.accept_9_6_5_3_1_205 6 68 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 68 75 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 68 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 75 (accept_3_4 4 68 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 68 75 (Polychromatic418967fa.accept_10_3_8_5_1_606 3 68 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 75 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 68
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 75 (accept_3_4 1 68 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68 75)))))))) (allB_succ' 9 67 75 (Eq.refl Bool.true)
  (allA_succ_of_accept 8 67 75 (accept_3_5 8 67 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 75
  (Polychromatic418967fa.accept_9_7_4_3_1_204 7 67 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 67 75 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 67 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 67 75 (accept_3_5 5 67 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 67 75 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 67 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 67 75 (Polychromatic418967fa.accept_10_3_7_5_1_288 3
  67 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 75 (accept_3_5 2 67 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 75 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 67
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67 75))))))))) (allB_succ' 10 66 75 (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 66 75 3 3 22 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 66 75 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 66 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 75 (Polychromatic418967fa.accept_16_7_2_11_1_931 7
  66 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 75 3 2 22 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 75
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 66 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 66 75 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 66 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 66 75 3 1 22 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 66 75 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 66 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 75
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 66 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 66 75)))))))))) (allB_succ' 11 65 75 (Eq.refl Bool.true) (allA_succ_of_gcd 10 65 75 5 2 13 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 65 75
  (Polychromatic418967fa.accept_12_9_5_3_1_782 9 65 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 65 75 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 65 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 75 (accept_3_4 7 65 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 65 75 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 65 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 65 75 5 1 13 15 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 65 75 (accept_3_4 4 65 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 65 75 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 65 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 75 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 65
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 75 (accept_3_4 1 65 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65 75))))))))))) (allB_succ' 12 64 75 (Eq.refl Bool.true)
  (allA_succ_of_accept 11 64 75 (accept_3_5 11 64 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 64
  75 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 64 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 64 75 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 64 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 64 75 (accept_3_5 8 64 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 64 75 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 64 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 64 75 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 64
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 64 75 (accept_3_5 5 64 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 64 75 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 64
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 64 75
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 64 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 64 75 (accept_3_5 2 64 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 64 75
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 64 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 64 75)))))))))))) (allB_succ' 13 63 75 (Eq.refl Bool.true) (allA_succ_of_gcd 12 63 75 3 4 21 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 63 75
  (Polychromatic418967fa.accept_19_11_6_18_1_2717 11 63 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 63 75 (Polychromatic418967fa.accept_11_10_8_9_1_492 10 63 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 63 75 3 3 21 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 63 75 (Polychromatic418967fa.accept_10_8_3_5_1_613 8 63 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 75
  (Polychromatic418967fa.accept_10_7_3_5_1_301 7 63 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 63 75 3 2 21 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 63 75 (Polychromatic418967fa.accept_17_5_12_7_1_2651 5 63 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 75 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 63 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 63 75 3 1 21 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 63 75
  (Polychromatic418967fa.accept_10_2_3_5_1_996 2 63 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 63 75 (Polychromatic418967fa.accept_13_1_11_10_1_1258 1 63 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 63 75))))))))))))) (allB_succ' 14 62 75 (Eq.refl Bool.true)
  (allA_succ_of_accept 13 62 75 (accept_3_4 13 62 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 62
  75 (Polychromatic418967fa.accept_18_12_8_3_1_1627 12 62 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 62 75 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 62 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 62 75 (accept_3_4 10 62 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 62 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 62 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 62 75
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 62 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 62 75 (accept_3_4 7 62 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 62 75
  (Polychromatic418967fa.accept_9_6_8_3_1_183 6 62 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 62 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 62 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 75 (accept_3_4 4 62 75 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 62 75 (Polychromatic418967fa.accept_10_3_2_5_1_295 3 62 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 75 (Polychromatic418967fa.accept_9_2_8_3_1_181 2 62 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 75 (accept_3_4 1 62 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 62 75)))))))))))))) (allB_succ' 15 61 75 (Eq.refl Bool.true)
  (allA_succ_of_accept 14 61 75 (accept_3_5 14 61 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 61
  75 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 61 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 61 75 (Polychromatic418967fa.accept_13_12_9_10_1_1223 12 61 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 61 75 (accept_3_5 11 61 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 61 75 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 61 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 61 75 (Polychromatic418967fa.accept_10_9_1_5_1_594 9
  61 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 75 (accept_3_5 8 61 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 75 (Polychromatic418967fa.accept_20_7_1_15_1_2700 7
  61 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 75
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 61 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 75 (accept_3_5 5 61 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61 75
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 61 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 75 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 61 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 75 (accept_3_5 2 61 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 75 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 61 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 75))))))))))))))) (allB_succ' 16 60 75 (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 60 75 15 1 4 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 60 75 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 60 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 75 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 60 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 75 3 4 20 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 75
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 60 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 60 75 5 2 12 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 60 75 3 3 20 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 60 75 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 60 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 75 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 60 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 75 3 2 20 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 60 75 5 1 12 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 60 75
  (Polychromatic418967fa.accept_9_4_6_3_1_179 4 60 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 60 75 3 1 20 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 60 75 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 60 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 75 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 60 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60 75)))))))))))))))) (allB_succ' 17 59 75
  (Eq.refl Bool.true) (allA_succ_of_accept 16 59 75 (accept_3_4 16 59 75 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 59 75 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 59 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 59 75 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 59 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 75 (accept_3_4 13 59 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 75 (Polychromatic418967fa.accept_13_12_7_10_1_2662
  12 59 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 75
  (Polychromatic418967fa.accept_9_2_5_3_1_37 11 59 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 75 (accept_3_4 10 59 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 59
  75 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 59 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 59 75 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 59 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 75 (accept_3_4 7 59 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 59 75 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 59 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 75 (Polychromatic418967fa.accept_19_5_2_18_1_2716 5
  59 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 75 (accept_3_4 4 59 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59 75 (Polychromatic418967fa.accept_13_3_7_10_1_668 3
  59 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 75
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 59 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 59 75 (accept_3_4 1 59 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59
  75))))))))))))))))) (allB_succ' 18 58 75 (Eq.refl Bool.true) (allA_succ_of_accept 17 58 75 (accept_3_5 17 58 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 58 75 (Polychromatic418967fa.accept_9_7_4_3_1_204 16
  58 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 58 75
  (Polychromatic418967fa.accept_9_6_4_3_1_203 15 58 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 58 75 (accept_3_5 14 58 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 58
  75 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 58 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 58 75 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 58 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 58 75 (accept_3_5 11 58 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 58 75 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 58 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 58 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 58
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 58 75 (accept_3_5 8 58 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 58 75 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 58
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 58 75
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 58 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 58 75 (accept_3_5 5 58 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 58 75
  (Polychromatic418967fa.accept_7_4_2_5_1_527 4 58 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 58 75 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 58 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 75 (accept_3_5 2 58 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 58 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 58 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58 75)))))))))))))))))) (allB_succ' 19 57 75 (Eq.refl Bool.true)
  (allA_succ_of_gcd 18 57 75 3 6 19 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 57 75 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 57 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 75 (Polychromatic418967fa.accept_17_16_6_7_1_2715 16 57 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 57 75 3 5 19 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 57 75
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 57 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 75 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 57 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 57 75 3 4 19 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 57 75 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 57 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 75
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 57 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 57 75 3 3 19 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 57 75 (Polychromatic418967fa.accept_10_8_7_5_1_602 8 57 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 75 (Polychromatic418967fa.accept_11_7_2_9_1_480 7 57 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 57 75 3 2 19 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 57 75
  (Polychromatic418967fa.accept_12_5_9_3_1_85 5 57 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 57 75 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 57 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 57 75 3 1 19 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 57 75 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 57 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 75
  (Polychromatic418967fa.accept_12_1_9_3_1_370 1 57 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 57 75))))))))))))))))))) (allB_succ' 20 56 75 (Eq.refl Bool.true) (allA_succ_of_accept 19 56 75 (accept_3_4
  19 56 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 56 75
  (Polychromatic418967fa.accept_12_6_8_3_1_82 18 56 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 56 75 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 56 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 75 (accept_3_4 16 56 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 56 75 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 56 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 75 (Polychromatic418967fa.accept_9_5_2_3_1_194 14
  56 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 56 75 (accept_3_4 13 56 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 56 75 (Polychromatic418967fa.accept_16_12_8_11_1_2695
  12 56 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 56 75
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 56 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 56 75 (accept_3_4 10 56 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 56
  75 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 56 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 56 75 (Polychromatic418967fa.accept_9_8_2_3_1_447 8 56 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 56 75 (accept_3_4 7 56 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 56 75 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 56 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 56 75 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 56
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 75 (accept_3_4 4 56 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 56 75 (Polychromatic418967fa.accept_16_3_8_11_1_2714 3
  56 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 75
  (Polychromatic418967fa.accept_21_2_14_12_1_2713 2 56 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 56 75 (accept_3_4 1 56 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56
  75)))))))))))))))))))) (allB_succ' 21 55 75 (Eq.refl Bool.true) (allA_succ_of_gcd 20 55 75 5 4 11 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 55 75
  (Polychromatic418967fa.accept_13_6_3_10_1_698 19 55 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 55 75 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 55 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 75 (accept_3_5 17 55 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 55 75 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 55 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 55 75 5 3 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 55 75 (accept_3_5 14 55 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 75 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 55 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 75
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 55 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 75 (accept_3_5 11 55 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 55 75
  5 2 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 55 75
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 55 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 55 75 (accept_3_5 8 55 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 75
  (Polychromatic418967fa.accept_9_7_1_3_1_443 7 55 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 55 75 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 55 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 55 75 5 1 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 55 75 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 55 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 75
  (Polychromatic418967fa.accept_16_3_7_11_1_1723 3 55 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 55 75 (accept_3_5 2 55 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 75
  (Polychromatic418967fa.accept_7_1_6_5_1_39 1 55 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 55 75))))))))))))))))))))) (allB_succ' 22 54 75 (Eq.refl Bool.true) (allA_succ_of_gcd 21 54 75 3 7 18 25
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 54 75
  (Polychromatic418967fa.accept_12_8_6_3_1_366 20 54 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 54 75 (Polychromatic418967fa.accept_10_9_4_5_1_616 19 54 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 75 3 6 18 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 54 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 75
  (Polychromatic418967fa.accept_10_6_4_5_1_615 16 54 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 54 75 3 5 18 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 54 75 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 54 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 54 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 75 3 4 18 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 75
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 11 54 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 54 75 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 54 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 54 75 3 3 18 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 54 75 (Polychromatic418967fa.accept_11_8_10_9_1_1401 8 54 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 75
  (Polychromatic418967fa.accept_14_7_12_5_1_1861 7 54 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 54 75 3 2 18 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 54 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 54 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 75 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 54 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 54 75 3 1 18 25 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 54 75
  (Polychromatic418967fa.accept_12_2_6_3_1_331 2 54 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 54 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 54 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 54 75)))))))))))))))))))))) (allB_succ' 23 53 75 (Eq.refl Bool.true)
  (allA_succ_of_accept 22 53 75 (accept_3_4 22 53 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 53
  75 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 53 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 53 75 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 53 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 75 (accept_3_4 19 53 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 53 75 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 53 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 75 (Polychromatic418967fa.accept_10_7_3_5_1_301 17
  53 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 75 (accept_3_4 16 53 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 53 75 (Polychromatic418967fa.accept_7_1_4_5_1_35 15
  53 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 75
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 53 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 53 75 (accept_3_4 13 53 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 53
  75 (Polychromatic418967fa.accept_10_2_3_5_1_996 12 53 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 53 75 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 53 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 75 (accept_3_4 10 53 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 53 75 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 53 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 75 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 53
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 75 (accept_3_4 7 53 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 75 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 53
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 75
  (Polychromatic418967fa.accept_9_5_8_3_1_437 5 53 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 75 (accept_3_4 4 53 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53 75
  (Polychromatic418967fa.accept_19_3_15_18_1_2682 3 53 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 75 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 53 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 75 (accept_3_4 1 53 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 75))))))))))))))))))))))) (allB_succ' 24 52 75 (Eq.refl Bool.true) (allA_succ_of_accept 23 52
  75 (accept_3_5 23 52 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 52 75
  (Polychromatic418967fa.accept_7_1_3_5_1_33 22 52 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 52 75 (Polychromatic418967fa.accept_11_10_8_9_1_492 21 52 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 52 75 (accept_3_5 20 52 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 52 75 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 52 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 52 75 (Polychromatic418967fa.accept_10_8_2_5_1_596 18
  52 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 52 75 (accept_3_5 17 52 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 52 75 (Polychromatic418967fa.accept_7_2_3_5_1_34 16
  52 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 52 75
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 52 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 52 75 (accept_3_5 14 52 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 52
  75 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 52 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 52 75 (Polychromatic418967fa.accept_14_12_10_5_1_2712 12 52 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 52 75 (accept_3_5 11 52 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 52 75 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 52 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 52 75 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 52
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 75 (accept_3_5 8 52 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 52 75 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 52
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 75
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 52 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 52 75 (accept_3_5 5 52 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52 75
  (Polychromatic418967fa.accept_9_4_7_3_1_43 4 52 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 52 75 (Polychromatic418967fa.accept_10_3_2_5_1_295 3 52 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 75 (accept_3_5 2 52 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 52 75 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 52 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52 75)))))))))))))))))))))))) (allB_succ' 25 51 75 (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 51 75 3 8 17 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 51 75 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 51 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 75 (Polychromatic418967fa.accept_9_4_6_3_1_179 22
  51 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 51 75 3 7 17 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 51 75
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 51 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 75 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 51 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 51 75 3 6 17 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 51 75 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 51 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 75
  (Polychromatic418967fa.accept_9_7_6_3_1_456 16 51 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 51 75 3 5 17 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 51 75 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 51 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 75 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 51 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 51 75 3 4 17 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 51 75
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 51 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 51 75 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 51 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 51 75 3 3 17 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 51 75 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 51 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 75
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 51 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 51 75 3 2 17 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 51 75 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 51 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 75 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 51 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 51 75 3 1 17 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 51 75
  (Polychromatic418967fa.accept_9_2_6_3_1_178 2 51 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 51 75 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 51 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 51 75))))))))))))))))))))))))) (allB_succ' 26 50 75 (Eq.refl Bool.true)
  (allA_succ_of_gcd 25 50 75 25 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 50 75 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 50 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 50 75 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 50 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 75 (accept_3_4 22 50 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 50
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 75 5 4 10 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 75 (accept_3_4 19 50
  75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 50 75 (Polychromatic418967fa.accept_7_4_1_5_1_540
  18 50 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 50 75
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 50 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 50 75 (accept_3_4 16 50 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 50 75
  5 3 10 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 50
  75 (Polychromatic418967fa.accept_11_3_6_9_1_1378 14 50 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 50 75 (accept_3_4 13 50 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 50
  75 (Polychromatic418967fa.accept_13_12_11_10_1_2711 12 50 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 50 75 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 50 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 50 75 5 2 10 15 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 50 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 50 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 75
  (Polychromatic418967fa.accept_9_8_5_3_1_777 8 50 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 50 75 (accept_3_4 7 50 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50 75
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 50 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 50 75 5 1 10 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 50 75 (accept_3_4 4 50 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 50 75
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 50 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 50 75 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 50 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 75 (accept_3_4 1 50 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 50 75)))))))))))))))))))))))))) (allB_succ' 27 49 75 (Eq.refl Bool.true) (allA_succ_of_accept 26
  49 75 (accept_3_5 26 49 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 75
  (Polychromatic418967fa.accept_9_7_4_3_1_204 25 49 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 49 75 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 49 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 75 (accept_3_5 23 49 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 49 75 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 49 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 75 (Polychromatic418967fa.accept_10_1_9_5_1_83 21
  49 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 75 (accept_3_5 20 49 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 75 (Polychromatic418967fa.accept_9_1_4_3_1_201 19
  49 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 75
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 49 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 75 (accept_3_5 17 49 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 49
  75 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 49 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 49 75 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 49 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 75 (accept_3_5 14 49 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 49 75 (Polychromatic418967fa.accept_27_13_22_21_1_2710 13 49 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 75
  (Polychromatic418967fa.accept_14_12_7_5_1_1107 12 49 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 49 75 (accept_3_5 11 49 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 49
  75 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 49 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 49 75 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 49 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 75 (accept_3_5 8 49 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 49 75 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 49 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 75 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 49
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 75 (accept_3_5 5 49 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49 75 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 49
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 75
  (Polychromatic418967fa.accept_19_3_11_18_1_2709 3 49 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 49 75 (accept_3_5 2 49 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 75
  (Polychromatic418967fa.accept_9_1_4_3_1_201 1 49 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 49 75))))))))))))))))))))))))))) (allB_succ' 28 48 75 (Eq.refl Bool.true) (allA_succ_of_gcd 27 48 75 3 9 16
  25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 48 75
  (Polychromatic418967fa.accept_18_8_12_3_1_2708 26 48 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 48 75 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 48 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 75 3 8 16 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 75 (Polychromatic418967fa.accept_10_3_8_5_1_606 23 48 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 48 75
  (Polychromatic418967fa.accept_7_1_6_5_1_39 22 48 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 48 75 3 7 16 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 48 75 (Polychromatic418967fa.accept_18_2_12_3_1_2707 20 48 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 75 (Polychromatic418967fa.accept_13_6_9_10_1_1201 19 48 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 75 3 6 16 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 75
  (Polychromatic418967fa.accept_10_7_8_5_1_1008 17 48 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 48 75 (Polychromatic418967fa.accept_21_16_6_12_1_2706 16 48 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 48 75 3 5 16 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 48 75 (Polychromatic418967fa.accept_13_1_9_10_1_625 14 48 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 75
  (Polychromatic418967fa.accept_10_3_8_5_1_606 13 48 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 48 75 3 4 16 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 48 75 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 48 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 48 75 (Polychromatic418967fa.accept_17_10_14_7_1_2679 10 48 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 48 75 3 3 16 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 48 75
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 48 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 48 75 (Polychromatic418967fa.accept_10_7_8_5_1_1008 7 48 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 75 3 2 16 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 75 (Polychromatic418967fa.accept_19_5_10_18_1_2705 5 48 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48 75
  (Polychromatic418967fa.accept_7_4_6_5_1_141 4 48 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 48 75 3 1 16 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 48 75 (Polychromatic418967fa.accept_10_2_8_5_1_587 2 48 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 75 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 48 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 75)))))))))))))))))))))))))))) (allB_succ'
  29 47 75 (Eq.refl Bool.true) (allA_succ_of_accept 28 47 75 (accept_3_4 28 47 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 47 75 (Polychromatic418967fa.accept_19_8_9_18_1_2704 27 47 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 47 75 (Polychromatic418967fa.accept_6_2_5_3_1_16 26
  47 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 75 (accept_3_4 25 47 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 75 (Polychromatic418967fa.accept_9_6_2_3_1_771 24
  47 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 75
  (Polychromatic418967fa.accept_9_5_2_3_1_194 23 47 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 75 (accept_3_4 22 47 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 47
  75 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 47 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 47 75 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 47 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 75 (accept_3_4 19 47 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 47 75 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 47 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 75 (Polychromatic418967fa.accept_9_8_2_3_1_447 17
  47 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 75 (accept_3_4 16 47 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 75 (Polychromatic418967fa.accept_9_6_2_3_1_771 15
  47 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 75
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 47 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 47 75 (accept_3_4 13 47 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 47
  75 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 47 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 47 75 (Polychromatic418967fa.accept_13_11_8_10_1_676 11 47 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 75 (accept_3_4 10 47 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 47 75 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 47 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 75 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 47
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 75 (accept_3_4 7 47 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 75 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 47
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 75
  (Polychromatic418967fa.accept_9_5_2_3_1_194 5 47 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 75 (accept_3_4 4 47 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47 75
  (Polychromatic418967fa.accept_10_3_7_5_1_288 3 47 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 75 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 47 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 75 (accept_3_4 1 47 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 75))))))))))))))))))))))))))))) (allB_succ' 30 46 75 (Eq.refl Bool.true) (allA_succ_of_accept
  29 46 75 (accept_3_5 29 46 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 75
  (Polychromatic418967fa.accept_19_9_8_18_1_1571 28 46 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 46 75 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 46 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 46 75 (accept_3_5 26 46 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 46 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 46 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 46 75 (Polychromatic418967fa.accept_9_6_1_3_1_191 24
  46 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 75 (accept_3_5 23 46 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 75 (Polychromatic418967fa.accept_7_1_4_5_1_35 22
  46 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 75
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 46 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 46 75 (accept_3_5 20 46 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 46
  75 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 46 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 46 75 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 46 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 75 (accept_3_5 17 46 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 46 75 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 46 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 75 (Polychromatic418967fa.accept_7_1_4_5_1_35 15
  46 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 46 75 (accept_3_5 14 46 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 46 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 46
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 46 75
  (Polychromatic418967fa.accept_13_12_7_10_1_2662 12 46 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 46 75 (accept_3_5 11 46 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 46
  75 (Polychromatic418967fa.accept_19_10_8_18_1_2669 10 46 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 46 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 46 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 46 75 (accept_3_5 8 46 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 46 75 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 46 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 46 75 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 46
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 75 (accept_3_5 5 46 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 46 75 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 46
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 75
  (Polychromatic418967fa.accept_13_3_7_10_1_668 3 46 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 46 75 (accept_3_5 2 46 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 75
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 46 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 46 75)))))))))))))))))))))))))))))) (allB_succ' 31 45 75 (Eq.refl Bool.true) (allA_succ_of_gcd 30 45 75 15 2
  3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 75
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 45 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 45 75 (Polychromatic418967fa.accept_13_2_6_10_1_2703 28 45 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 45 75 3 9 15 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 45 75 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 45 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 45 75 5 5 9 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 45 75 3 8 15 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 75
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 45 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 45 75 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 45 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 45 75 3 7 15 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 45 75 5 4 9 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 45 75 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 45 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 45 75 3 6 15 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 45 75
  (Polychromatic418967fa.accept_12_5_9_3_1_85 17 45 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 45 75 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 45 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 75 15 1 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 75 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 45 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 75
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 45 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 45 75 3 4 15 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 45 75 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 45 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 45 75 5 2 9 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 45 75 3 3 15 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 45 75 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 45 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 75
  (Polychromatic418967fa.accept_12_7_9_3_1_767 7 45 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 45 75 3 2 15 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 45 75 5 1 9 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 45 75 (Polychromatic418967fa.accept_13_4_6_10_1_1199 4 45 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 45 75 3 1 15 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 45 75 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 45 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 75
  (Polychromatic418967fa.accept_7_1_3_5_1_33 1 45 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 45 75))))))))))))))))))))))))))))))) (allB_succ' 32 44 75 (Eq.refl Bool.true) (allA_succ_of_accept 31 44 75
  (accept_3_4 31 44 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 44 75
  (Polychromatic418967fa.accept_12_6_8_3_1_82 30 44 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 44 75 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 44 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 75 (accept_3_4 28 44 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 44 75 (Polychromatic418967fa.accept_18_9_8_3_1_2702 27 44 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 75 (Polychromatic418967fa.accept_10_6_4_5_1_615 26
  44 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 44 75 (accept_3_4 25 44 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 44 75 (Polychromatic418967fa.accept_7_3_2_5_1_147 24
  44 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 44 75
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 44 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 44 75 (accept_3_4 22 44 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 44
  75 (Polychromatic418967fa.accept_10_1_4_5_1_1031 21 44 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 44 75 (Polychromatic418967fa.accept_9_2_8_3_1_181 20 44 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 44 75 (accept_3_4 19 44 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 44 75 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 44 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 44 75 (Polychromatic418967fa.accept_6_5_2_3_1_81 17
  44 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 75 (accept_3_4 16 44 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 44 75 (Polychromatic418967fa.accept_8_7_4_3_1_156 15
  44 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 75
  (Polychromatic418967fa.accept_9_5_8_3_1_437 14 44 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 44 75 (accept_3_4 13 44 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 44
  75 (Polychromatic418967fa.accept_18_12_8_3_1_1627 12 44 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 44 75 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 44 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 75 (accept_3_4 10 44 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 44 75 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 44 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 75
  (Polychromatic418967fa.accept_13_8_5_10_1_2701 8 44 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 44 75 (accept_3_4 7 44 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44 75
  (Polychromatic418967fa.accept_9_6_8_3_1_183 6 44 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 44 75 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 44 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 44 75 (accept_3_4 4 44 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 44 75 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 44 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 44 75 (Polychromatic418967fa.accept_9_2_8_3_1_181 2 44
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 75 (accept_3_4 1 44 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 75)))))))))))))))))))))))))))))))) (allB_succ' 33 43 75 (Eq.refl
  Bool.true) (allA_succ_of_accept 32 43 75 (accept_3_5 32 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 43 75 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 43 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 75 (Polychromatic418967fa.accept_11_8_10_9_1_1401 30 43 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 75 (accept_3_5 29 43 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 43 75 (Polychromatic418967fa.accept_6_4_1_3_1_77 28
  43 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 75
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 43 75 (accept_3_5 26 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 43
  75 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 43 75 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 43 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 43 75 (accept_3_5 23 43 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 43 75 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 43 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 75 (Polychromatic418967fa.accept_12_9_7_3_1_1309
  21 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 75 (accept_3_5 20 43
  75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 75 (Polychromatic418967fa.accept_9_1_7_3_1_41
  19 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 75
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 75 (accept_3_5 17 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 43
  75 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 43 75 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 43 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 75 (accept_3_5 14 43 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 43 75 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 43 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 75 (Polychromatic418967fa.accept_10_2_3_5_1_996 12
  43 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 75 (accept_3_5 11 43 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 43 75 (Polychromatic418967fa.accept_6_4_1_3_1_77 10
  43 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 75
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 43 75 (accept_3_5 8 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 75
  (Polychromatic418967fa.accept_10_7_3_5_1_301 7 43 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 43 75 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 43 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 43 75 (accept_3_5 5 43 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 43 75 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 43 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 43 75 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 43
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 75 (accept_3_5 2 43 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 75 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 43
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 75)))))))))))))))))))))))))))))))))
  (allB_succ' 34 42 75 (Eq.refl Bool.true) (allA_succ_of_gcd 33 42 75 3 11 14 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 42 75 (Polychromatic418967fa.accept_9_5_6_3_1_40 32 42
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 75
  (Polychromatic418967fa.accept_9_4_6_3_1_179 31 42 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 42 75 3 10 14 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 42 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 42 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 42 75 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 42 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 42 75 3 9 14 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 42 75
  (Polychromatic418967fa.accept_9_8_6_3_1_457 26 42 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 42 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 42 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 75 3 8 14 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 75 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 42 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 42 75
  (Polychromatic418967fa.accept_9_4_6_3_1_179 22 42 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 42 75 3 7 14 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 42 75 (Polychromatic418967fa.accept_9_2_6_3_1_178 20 42 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 75 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 42 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 75 3 6 14 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 75
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 42 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 42 75 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 42 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 42 75 3 5 14 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 42 75 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 42 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 75
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 42 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 42 75 3 4 14 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 42 75 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 42 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 42 75 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 42 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 42 75 3 3 14 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 42 75
  (Polychromatic418967fa.accept_9_8_6_3_1_457 8 42 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 42 75 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 42 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 75 3 2 14 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 42 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42 75
  (Polychromatic418967fa.accept_9_4_6_3_1_179 4 42 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 42 75 3 1 14 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 42 75 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 42 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 42 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 75))))))))))))))))))))))))))))))))))
  (allB_succ' 35 41 75 (Eq.refl Bool.true) (allA_succ_of_accept 34 41 75 (accept_3_4 34 41 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 75 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 41 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 75
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 75 (accept_3_4 31 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 41
  75 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 41 75 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 41 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 75 (accept_3_4 28 41 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 41 75 (Polychromatic418967fa.accept_20_7_1_15_1_2700 27 41 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 75 (Polychromatic418967fa.accept_4_2_1_3_1_27 26
  41 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 75 (accept_3_4 25 41 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 75 (Polychromatic418967fa.accept_9_6_5_3_1_205 24
  41 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 75
  (Polychromatic418967fa.accept_19_4_3_18_1_2699 23 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 75 (accept_3_4 22 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 41
  75 (Polychromatic418967fa.accept_11_10_8_9_1_492 21 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 41 75 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 41 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 75 (accept_3_4 19 41 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 41 75 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 41 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 75 (Polychromatic418967fa.accept_9_8_5_3_1_777 17
  41 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 75 (accept_3_4 16 41 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 75 (Polychromatic418967fa.accept_7_1_6_5_1_39 15
  41 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 75
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 75 (accept_3_4 13 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 41
  75 (Polychromatic418967fa.accept_13_12_2_10_1_2698 12 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 41 75 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 41 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 75 (accept_3_4 10 41 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 75 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 41 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 75
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 75 (accept_3_4 7 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 75
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 41 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 41 75 (Polychromatic418967fa.accept_13_5_2_10_1_248 5 41 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 75 (accept_3_4 4 41 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 41 75 (Polychromatic418967fa.accept_13_3_2_10_1_2697 3 41 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 75 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 41
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 75 (accept_3_4 1 41 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41 75))))))))))))))))))))))))))))))))))) (allB_succ' 36 40 75
  (Eq.refl Bool.true) (allA_succ_of_gcd 35 40 75 5 7 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 40 75 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 40 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 75
  (Polychromatic418967fa.accept_9_6_4_3_1_203 33 40 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 40 75 (accept_3_5 32 40 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 40
  75 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 40 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 40 75 5 6 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 40 75 (accept_3_5 29 40 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 40
  75 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 40 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 40 75 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 40 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 40 75 (accept_3_5 26 40 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 40 75 5 5 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 24 40 75 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 40 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 75 (accept_3_5 23 40 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 75 (Polychromatic418967fa.accept_13_9_1_10_1_647 22 40 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 75
  (Polychromatic418967fa.accept_14_7_12_5_1_1861 21 40 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 40 75 5 4 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 40 75 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 40 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 40 75 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 40 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 75 (accept_3_5 17 40 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 40 75 (Polychromatic418967fa.accept_9_7_4_3_1_204 16
  40 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 40 75 5 3 8 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 40 75 (accept_3_5 14 40
  75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 40 75 (Polychromatic418967fa.accept_6_1_4_3_1_14
  13 40 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 40 75
  (Polychromatic418967fa.accept_16_12_8_11_1_2695 12 40 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 40 75 (accept_3_5 11 40 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40 75
  5 2 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 40 75
  (Polychromatic418967fa.accept_13_9_1_10_1_647 9 40 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 40 75 (accept_3_5 8 40 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40 75
  (Polychromatic418967fa.accept_6_1_4_3_1_14 7 40 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 40 75 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 40 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 40 75 5 1 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 40 75 (Polychromatic418967fa.accept_13_4_1_10_1_693 4 40 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 75
  (Polychromatic418967fa.accept_14_3_12_5_1_153 3 40 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 40 75 (accept_3_5 2 40 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40 75
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 40 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 40 75)))))))))))))))))))))))))))))))))))) (allB_succ' 37 39 75 (Eq.refl Bool.true) (allA_succ_of_gcd 36 39
  75 3 12 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  39 75 (Polychromatic418967fa.accept_16_3_7_11_1_1723 35 39 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 39 75 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 39 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 39 75 3 11 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 39 75 (Polychromatic418967fa.accept_17_15_5_7_1_2694
  32 39 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 75
  (Polychromatic418967fa.accept_10_1_9_5_1_83 31 39 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 39 75 3 10 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 39 75 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 39 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 75 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 39 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 75 3 9 13 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 75
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 26 39 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 75 (Polychromatic418967fa.accept_11_3_6_9_1_1378 25 39 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 39 75 3 8 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 39 75 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 39 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 75
  (Polychromatic418967fa.accept_7_1_4_5_1_35 22 39 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 39 75 3 7 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 39 75 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 39 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 75 (Polychromatic418967fa.accept_16_3_7_11_1_1723 19 39 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 75 3 6 13 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 75
  (Polychromatic418967fa.accept_19_17_1_18_1_2693 17 39 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 39 75 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 39 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 39 75 3 5 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 39 75 (Polychromatic418967fa.accept_10_4_9_5_1_84 14 39 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 75
  (Polychromatic418967fa.accept_7_6_4_5_1_314 13 39 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 39 75 3 4 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 39 75 (Polychromatic418967fa.accept_10_1_9_5_1_83 11 39 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 75 (Polychromatic418967fa.accept_20_10_19_15_1_2692 10 39
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 75 3 3 13 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 75
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 39 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 75 (Polychromatic418967fa.accept_19_7_1_18_1_2691 7 39 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 39 75 3 2 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 39 75 (Polychromatic418967fa.accept_16_5_7_11_1_2664 5 39 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 75
  (Polychromatic418967fa.accept_8_4_7_3_1_144 4 39 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 39 75 3 1 13 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 39 75 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 39 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 75 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 39 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 75)))))))))))))))))))))))))))))))))))))
  (allB_succ 38 75 (allA_succ_of_accept 37 38 75 (accept_3_4 37 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 38 75 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 38 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 38 75 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 38 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 75 (accept_3_4 34 38 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 38
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 75
  (Polychromatic418967fa.accept_9_5_2_3_1_194 32 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 75 (accept_3_4 31 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 38
  75 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 38 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 38 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 75 (accept_3_4 28 38 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 38 75 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 38 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 75 (Polychromatic418967fa.accept_9_8_2_3_1_447 26
  38 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 38 75 (accept_3_4 25 38 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 38 75 (Polychromatic418967fa.accept_9_6_2_3_1_771 24
  38 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 38 75
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 38 75 (accept_3_4 22 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 38
  75 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 38 75 (Polychromatic418967fa.accept_13_7_12_10_1_640 20 38 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 38 75 (accept_3_4 19 38 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 38 75 (Polychromatic418967fa.accept_11_7_5_9_1_884 18 38 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 38 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 38
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 75 (accept_3_4 16 38 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 75 (Polychromatic418967fa.accept_7_1_3_5_1_33 15
  38 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 75
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 75 (accept_3_4 13 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 38
  75 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 38 75 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 38 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 75 (accept_3_4 10 38 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 38 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 38 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 75 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 38
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 38 75 (accept_3_4 7 38 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38 75 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 38
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 38 75
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 38 75 (accept_3_4 4 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 38 75
  (Polychromatic418967fa.accept_10_3_8_5_1_606 3 38 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 38 75 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 38 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 75 (accept_3_4 1 38 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 38 75)))))))))))))))))))))))))))))))))))))) (allB_succ 37 75 (allA_succ_of_accept 36 37 75
  (Polychromatic418967fa.accept_24_12_13_3_1_351 36 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 75 (accept_3_5 35 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 37
  75 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 37 75 (Polychromatic418967fa.accept_9_6_1_3_1_191 33 37 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 75 (accept_3_5 32 37 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 37 75 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 37 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 75 (Polychromatic418967fa.accept_4_2_1_3_1_27 30
  37 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 75 (accept_3_5 29 37 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 37 75 (Polychromatic418967fa.accept_6_4_1_3_1_77 28
  37 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 75
  (Polychromatic418967fa.accept_13_1_11_10_1_1258 27 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 37 75 (accept_3_5 26 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37
  75 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 37 75 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 37 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 75 (accept_3_5 23 37 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 37 75 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 37 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 75 (Polychromatic418967fa.accept_12_9_1_3_1_350 21
  37 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 75 (accept_3_5 20 37 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 75
  (Polychromatic418967fa.accept_20_19_17_15_1_2690 19 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 37 75 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 37 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 75 (accept_3_5 17 37 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 37 75 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 37 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 75 (Polychromatic418967fa.accept_9_6_1_3_1_191 15
  37 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 75 (accept_3_5 14 37 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 75 (Polychromatic418967fa.accept_9_4_1_3_1_190 13
  37 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 75
  (Polychromatic418967fa.accept_10_2_7_5_1_605 12 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 75 (accept_3_5 11 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 37
  75 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 37 75 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 37 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 75 (accept_3_5 8 37 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 37 75 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 37 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 75 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 37
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 75 (accept_3_5 5 37 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37 75 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 37
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 75
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 37 75 (accept_3_5 2 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37 75
  (Polychromatic418967fa.accept_13_1_11_10_1_1258 1 37 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 37 75))))))))))))))))))))))))))))))))))))) (allB_succ 36 75 (allA_succ_of_accept 35 36 75
  (Polychromatic418967fa.accept_19_16_17_18_1_2688 35 36 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 75 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 36 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 36 75 3 11 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 36 75 (Polychromatic418967fa.accept_7_4_1_5_1_540 32 36 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 75
  (Polychromatic418967fa.accept_7_3_1_5_1_44 31 36 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 36 75 3 10 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 36 75 (Polychromatic418967fa.accept_10_9_6_5_1_1002 29 36 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 75 (Polychromatic418967fa.accept_11_6_3_9_1_906 28 36 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 36 75 3 9 12 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 36 75
  (Polychromatic418967fa.accept_17_9_2_7_1_2689 26 36 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 36 75 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 36 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 75 3 8 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 75 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 36 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 36 75
  (Polychromatic418967fa.accept_16_6_4_11_1_1719 22 36 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 36 75 3 7 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 36 75 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 36 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 75 (Polychromatic418967fa.accept_10_9_6_5_1_1002 19 36 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 75 3 6 12 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 75
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 36 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 36 75 (Polychromatic418967fa.accept_19_16_17_18_1_2688 16 36 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 36 75 3 5 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 36 75 (Polychromatic418967fa.accept_10_4_6_5_1_74 14 36 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 75
  (Polychromatic418967fa.accept_7_6_1_5_1_322 13 36 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 36 75 3 4 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 36 75 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 36 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 36 75 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 36 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 36 75 3 3 12 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 36 75
  (Polychromatic418967fa.accept_16_8_4_11_1_2687 8 36 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 36 75 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 36 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 75 3 2 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 75 (Polychromatic418967fa.accept_19_5_17_18_1_2686 5 36 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36 75
  (Polychromatic418967fa.accept_7_4_1_5_1_540 4 36 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 36 75 3 1 12 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 36 75 (Polychromatic418967fa.accept_27_2_9_21_1_2685 2 36 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 75 (Polychromatic418967fa.accept_10_1_6_5_1_304 1 36 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 75))))))))))))))))))))))))))))))))))))
  (allB_succ 35 75 (allA_succ_of_accept 34 35 75 (accept_3_4 34 35 75 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 35 75 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 35 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 35 75 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 35 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 75 (accept_3_4 31 35 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 35 75 5 6 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 35 75 (Polychromatic418967fa.accept_9_2_8_3_1_181 29
  35 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 75 (accept_3_4 28 35 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 75 (Polychromatic418967fa.accept_13_1_9_10_1_625
  27 35 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 75
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 35 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 35 75 5 5 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 35 75 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 35 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 75 (Polychromatic418967fa.accept_9_5_8_3_1_437 23 35 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 75 (accept_3_4 22 35 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 75 (Polychromatic418967fa.accept_12_9_11_3_1_772
  21 35 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 35 75 5 4 7 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 35 75 (accept_3_4 19 35
  75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 75 (Polychromatic418967fa.accept_11_7_2_9_1_480
  18 35 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 75
  (Polychromatic418967fa.accept_19_17_16_18_1_2684 17 35 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 35 75 (accept_3_4 16 35 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 35 75
  5 3 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 35 75
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 35 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 35 75 (accept_3_4 13 35 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 35
  75 (Polychromatic418967fa.accept_13_12_9_10_1_1223 12 35 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 35 75 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 35 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 35 75 5 2 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 35 75 (Polychromatic418967fa.accept_12_9_11_3_1_772 9
  35 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 75
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 35 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 35 75 (accept_3_4 7 35 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 75
  (Polychromatic418967fa.accept_9_6_8_3_1_183 6 35 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 35 75 5 1 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 35 75 (accept_3_4 4 35 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 75
  (Polychromatic418967fa.accept_19_3_16_18_1_2683 3 35 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 35 75 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 35 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 75 (accept_3_4 1 35 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 35 75))))))))))))))))))))))))))))))))))) (allB_succ 34 75 (allA_succ_of_accept 33 34 75
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 34 75 (accept_3_5 32 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 34
  75 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 34 75 (Polychromatic418967fa.accept_12_6_10_3_1_1313 30 34 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 75 (accept_3_5 29 34 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 34 75 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 34 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 75 (Polychromatic418967fa.accept_14_13_6_5_1_1853
  27 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 34 75 (accept_3_5 26 34
  75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 34 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 25
  34 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 34 75
  (Polychromatic418967fa.accept_9_6_7_3_1_436 24 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 34 75 (accept_3_5 23 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 34
  75 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 34 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 34 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 34 75 (accept_3_5 20 34 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 34 75 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 34 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 34 75 (Polychromatic418967fa.accept_7_4_6_5_1_141 18
  34 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 75 (accept_3_5 17 34 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 75 (Polychromatic418967fa.accept_10_6_4_5_1_615 16
  34 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 75
  (Polychromatic418967fa.accept_7_1_6_5_1_39 15 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 75 (accept_3_5 14 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 34
  75 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 34 75 (Polychromatic418967fa.accept_13_12_8_10_1_1879 12 34 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 75 (accept_3_5 11 34 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 34 75 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 34 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 34
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 34 75 (accept_3_5 8 34 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34 75 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 34
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 34 75
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 34 75 (accept_3_5 5 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 34 75
  (Polychromatic418967fa.accept_7_4_6_5_1_141 4 34 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 34 75 (Polychromatic418967fa.accept_19_3_15_18_1_2682 3 34 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 75 (accept_3_5 2 34 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 34 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 34 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 75)))))))))))))))))))))))))))))))))) (allB_succ 33 75
  (allA_succ_of_accept 32 33 75 (Polychromatic418967fa.accept_9_5_6_3_1_40 32 33 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 75 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 33 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 33 75 3 10 11 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 33 75
  (Polychromatic418967fa.accept_9_2_6_3_1_178 29 33 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 33 75 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 33 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 33 75 3 9 11 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 33 75 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 33 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 75
  (Polychromatic418967fa.accept_9_7_6_3_1_456 25 33 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 33 75 3 8 11 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 33 75 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 33 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 75 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 33 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 33 75 3 7 11 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 33 75
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 33 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 75 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 33 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 33 75 3 6 11 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 33 75 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 33 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 75
  (Polychromatic418967fa.accept_9_7_6_3_1_456 16 33 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 33 75 3 5 11 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 33 75 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 33 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 75 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 33 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 33 75 3 4 11 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 33 75
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 33 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 33 75 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 33 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 33 75 3 3 11 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 33 75 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 33 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 75
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 33 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 33 75 3 2 11 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 33 75 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 33 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 75 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 33 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 33 75 3 1 11 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 33 75
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 33 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 33 75 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 33 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 33 75))))))))))))))))))))))))))))))))) (allB_succ 32 75 (allA_succ_of_accept
  31 32 75 (accept_3_4 31 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 32 75
  (Polychromatic418967fa.accept_7_2_4_5_1_313 30 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 32 75 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 32 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 75 (accept_3_4 28 32 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 32 75 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 32 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 75 (Polychromatic418967fa.accept_9_8_5_3_1_777 26
  32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 32 75 (accept_3_4 25 32 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 32 75 (Polychromatic418967fa.accept_9_6_5_3_1_205 24
  32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 32 75
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 32 75 (accept_3_4 22 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 32
  75 (Polychromatic418967fa.accept_22_21_10_9_1_2681 21 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 32 75 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 32 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 32 75 (accept_3_4 19 32 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 32 75 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 32 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 32 75
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 32 75 (accept_3_4 16 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 32
  75 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 32 75 (Polychromatic418967fa.accept_19_14_13_18_1_2680 14 32 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 32 75 (accept_3_4 13 32 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 32 75 (Polychromatic418967fa.accept_11_1_10_9_1_871 12 32 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 32 75 (Polychromatic418967fa.accept_6_5_2_3_1_81 11
  32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 75 (accept_3_4 10 32 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 75 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 32
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 75
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 75 (accept_3_4 7 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32 75
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 32 75 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 32 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 75 (accept_3_4 4 32 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 32 75 (Polychromatic418967fa.accept_10_3_2_5_1_295 3 32 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 75 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 32
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 75 (accept_3_4 1 32 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 75)))))))))))))))))))))))))))))))) (allB_succ 31 75
  (allA_succ_of_accept 30 31 75 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 31 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 75 (accept_3_5 29 31 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 75 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 31 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 75 (Polychromatic418967fa.accept_17_10_14_7_1_2679
  27 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 75 (accept_3_5 26 31
  75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 75 (Polychromatic418967fa.accept_9_7_4_3_1_204
  25 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 75
  (Polychromatic418967fa.accept_9_6_4_3_1_203 24 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 75 (accept_3_5 23 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 31
  75 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 31 75 (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 31 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 75 (accept_3_5 20 31 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 31 75 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 31 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 75 (Polychromatic418967fa.accept_26_18_5_23_1_2678
  18 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 75 (accept_3_5 17 31
  75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 31 75 (Polychromatic418967fa.accept_6_4_1_3_1_77
  16 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 75
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 31 75 (accept_3_5 14 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 31
  75 (Polychromatic418967fa.accept_19_13_12_18_1_2677 13 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 31 75 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 31 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 75 (accept_3_5 11 31 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 31 75 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 31 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 75
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 31 75 (accept_3_5 8 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 75
  (Polychromatic418967fa.accept_9_7_4_3_1_204 7 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 31 75 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 31 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 31 75 (accept_3_5 5 31 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 31 75 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 31 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 31 75 (Polychromatic418967fa.accept_16_3_15_11_1_2676
  3 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 75 (accept_3_5 2 31 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 75 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 31
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 75)))))))))))))))))))))))))))))))
  (allB_succ 30 75 (allA_succ_of_accept 29 30 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 30 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 30 75 (Polychromatic418967fa.accept_12_4_6_3_1_332 28
  30 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 30 75 3 9 10 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 30 75
  (Polychromatic418967fa.accept_12_2_6_3_1_331 26 30 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 30 75 5 5 6 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 30 75 3 8 10 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 30 75 (Polychromatic418967fa.accept_17_6_13_7_1_272 23 30 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 75 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 30 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 30 75 3 7 10 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 30 75 5 4 6 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 75
  (Polychromatic418967fa.accept_13_6_4_10_1_660 19 30 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 30 75 3 6 10 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 30 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 30 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 30 75 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 30 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 30 75 15 1 2 5 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 30 75
  (Polychromatic418967fa.accept_12_2_6_3_1_331 14 30 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 30 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 30 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 75 3 4 10 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 75 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 30 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 75 5 2 6 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 30 75 3 3 10 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 30 75
  (Polychromatic418967fa.accept_12_8_6_3_1_366 8 30 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 30 75 (Polychromatic418967fa.accept_13_7_4_10_1_2675 7 30 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 75 3 2 10 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 30 75 5 1 6 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 30 75 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 30 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 30 75 3 1 10 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 30 75
  (Polychromatic418967fa.accept_12_2_6_3_1_331 2 30 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 30 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 30 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 30 75)))))))))))))))))))))))))))))) (allB_succ 29 75 (allA_succ_of_accept 28 29 75
  (accept_3_4 28 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 75
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 75 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 29 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 75 (accept_3_4 25 29 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 75 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 29 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 75 (Polychromatic418967fa.accept_9_5_2_3_1_194 23
  29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 75 (accept_3_4 22 29 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 75 (Polychromatic418967fa.accept_10_1_9_5_1_83 21
  29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 75
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 29 75 (accept_3_4 19 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 29
  75 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 29 75 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 29 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 75 (accept_3_4 16 29 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 29 75 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 29 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 75 (Polychromatic418967fa.accept_4_2_1_3_1_27 14
  29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 75 (accept_3_4 13 29 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 75 (Polychromatic418967fa.accept_24_12_5_3_1_2674
  12 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 75
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 75 (accept_3_4 10 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 29
  75 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 29 75 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 29 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 75 (accept_3_4 7 29 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 29 75 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 29 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 75 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 29
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 75 (accept_3_4 4 29 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29 75 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 29
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 75
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 29 75 (accept_3_4 1 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29
  75))))))))))))))))))))))))))))) (allB_succ 28 75 (allA_succ_of_accept 27 28 75
  (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 28 75 (accept_3_5 26 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 28
  75 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 28 75 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 28 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 75 (accept_3_5 23 28 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 28 75 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 28 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 28 75 (Polychromatic418967fa.accept_13_8_2_10_1_652
  21 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 28 75 (accept_3_5 20 28
  75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 28 75 (Polychromatic418967fa.accept_6_1_4_3_1_14
  19 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 28 75
  (Polychromatic418967fa.accept_12_6_4_3_1_361 18 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 28 75 (accept_3_5 17 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 28
  75 (Polychromatic418967fa.accept_9_7_1_3_1_443 16 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 28 75 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 28 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 28 75 (accept_3_5 14 28 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 28 75 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 28 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 28 75 (Polychromatic418967fa.accept_10_2_8_5_1_587 12
  28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 28 75 (accept_3_5 11 28 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 28 75 (Polychromatic418967fa.accept_16_10_12_11_1_346
  10 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 28 75
  (Polychromatic418967fa.accept_30_9_28_15_1_2673 9 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 28 75 (accept_3_5 8 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 28 75
  (Polychromatic418967fa.accept_6_1_4_3_1_14 7 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 28 75 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 28 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 28 75 (accept_3_5 5 28 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 28 75 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 28 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 28 75 (Polychromatic418967fa.accept_10_3_8_5_1_606 3
  28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 75 (accept_3_5 2 28 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 28 75 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 28
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 75)))))))))))))))))))))))))))) (allB_succ
  27 75 (allA_succ_of_accept 26 27 75 (Polychromatic418967fa.accept_18_8_9_3_1_2645 26 27 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 75 (Polychromatic418967fa.accept_7_4_6_5_1_141 25
  27 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 27 75 3 8 9 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 27 75
  (Polychromatic418967fa.accept_10_3_7_5_1_288 23 27 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 27 75 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 27 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 27 75 3 7 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 27 75 (Polychromatic418967fa.accept_14_6_13_5_1_534 20 27 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 75
  (Polychromatic418967fa.accept_18_1_9_3_1_2672 19 27 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 27 75 3 6 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 27 75 (Polychromatic418967fa.accept_13_4_1_10_1_693 17 27 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 75 (Polychromatic418967fa.accept_17_16_10_7_1_2671 16 27 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 27 75 3 5 9 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 27 75
  (Polychromatic418967fa.accept_17_14_10_7_1_2670 14 27 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 75 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 27 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 27 75 3 4 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 27 75 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 27 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 75
  (Polychromatic418967fa.accept_19_10_8_18_1_2669 10 27 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 27 75 3 3 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 27 75 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 27 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 75 (Polychromatic418967fa.accept_11_7_5_9_1_884 7 27 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 27 75 3 2 9 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 27 75
  (Polychromatic418967fa.accept_20_5_7_15_1_2668 5 27 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 27 75 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 27 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 27 75 3 1 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 27 75 (Polychromatic418967fa.accept_10_2_7_5_1_605 2 27 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 75
  (Polychromatic418967fa.accept_7_1_6_5_1_39 1 27 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 27 75))))))))))))))))))))))))))) (allB_succ 26 75 (allA_succ_of_accept 25 26 75 (accept_3_4 25 26 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 75 (Polychromatic418967fa.accept_9_6_8_3_1_183 24
  26 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 26 75
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 26 75 (accept_3_4 22 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 26
  75 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 26 75 (Polychromatic418967fa.accept_9_2_8_3_1_181 20 26 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 75 (accept_3_4 19 26 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 26 75 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 26 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 26 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 26
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 75 (accept_3_4 16 26 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 26 75 (Polychromatic418967fa.accept_9_6_8_3_1_183 15
  26 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 75
  (Polychromatic418967fa.accept_9_5_8_3_1_437 14 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 26 75 (accept_3_4 13 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 26
  75 (Polychromatic418967fa.accept_16_12_10_11_1_2667 12 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 26 75 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 26 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 26 75 (accept_3_4 10 26 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 26 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 26 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 75
  (Polychromatic418967fa.accept_19_8_7_18_1_1595 8 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 26 75 (accept_3_4 7 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26 75
  (Polychromatic418967fa.accept_9_6_8_3_1_183 6 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 26 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 75 (accept_3_4 4 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 26 75 (Polychromatic418967fa.accept_14_3_12_5_1_153 3 26 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 75 (Polychromatic418967fa.accept_9_2_8_3_1_181 2 26 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 75 (accept_3_4 1 26 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 26 75)))))))))))))))))))))))))) (allB_succ 25 75 (allA_succ_of_accept 24 25
  75 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 25 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 75 (accept_3_5 23 25 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 25
  75 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 25 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 25 75 (Polychromatic418967fa.accept_12_9_1_3_1_350 21 25 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 25 75 5 4 5 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 25 75 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 25 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 75
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 25 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 75 (accept_3_5 17 25 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 25
  75 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 25 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 25 75 5 3 5 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 25 75 (accept_3_5 14 25 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 25
  75 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 25 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 25 75 (Polychromatic418967fa.accept_18_12_7_3_1_2666 12 25 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 75 (accept_3_5 11 25 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 25 75 5 2 5 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 25 75 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 25 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 75 (accept_3_5 8 25 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 25 75 (Polychromatic418967fa.accept_13_7_12_10_1_640 7 25 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 75 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 25
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 25 75 5 1 5 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 25 75
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 25 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 25 75 (Polychromatic418967fa.accept_19_3_6_18_1_2665 3 25 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 75 (accept_3_5 2 25 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 25 75 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 25 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 75))))))))))))))))))))))))) (allB_succ 24 75
  (allA_succ_of_accept 23 24 75 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 24 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 75 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 24 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 24 75 3 7 8 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 24 75
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 24 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 24 75 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 24 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 75 3 6 8 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 75 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 24 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 75
  (Polychromatic418967fa.accept_7_2_3_5_1_34 16 24 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 24 75 3 5 8 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 24 75 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 24 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 75 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 24 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 75 3 4 8 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 75
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 24 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 24 75 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 24 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 24 75 3 3 8 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 24 75 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 24 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 75
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 24 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 24 75 3 2 8 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 24 75 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 24 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 75 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 24 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 24 75 3 1 8 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 24 75
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 24 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 24 75 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 24 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 24 75)))))))))))))))))))))))) (allB_succ 23 75 (allA_succ_of_accept 22 23 75
  (accept_3_4 22 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 75
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 75 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 23 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 75 (accept_3_4 19 23 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 75 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 23 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 75 (Polychromatic418967fa.accept_7_3_2_5_1_147 17
  23 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 75 (accept_3_4 16 23 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 75 (Polychromatic418967fa.accept_9_6_5_3_1_205 15
  23 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 75
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 75 (accept_3_4 13 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 23
  75 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 23 75 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 23 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 75 (accept_3_4 10 23 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 23 75 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 23 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 75 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 23
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 75 (accept_3_4 7 23 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 75 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 23
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 75
  (Polychromatic418967fa.accept_16_5_7_11_1_2664 5 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 75 (accept_3_4 4 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23 75
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 23 75 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 23 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 75 (accept_3_4 1 23 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 23 75))))))))))))))))))))))) (allB_succ 22 75 (allA_succ_of_accept 21 22 75
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 75 (accept_3_5 20 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 22
  75 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 22 75 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 22 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 75 (accept_3_5 17 22 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 22 75 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 22 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 75 (Polychromatic418967fa.accept_9_6_4_3_1_203 15
  22 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 22 75 (accept_3_5 14 22 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 22 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 22
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 22 75
  (Polychromatic418967fa.accept_13_12_9_10_1_1223 12 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 22 75 (accept_3_5 11 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 22
  75 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 22 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 8 22 75 (accept_3_5 8 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 22 75 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 22 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 22 75 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 22 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 75 (accept_3_5 5 22 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 22 75 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 22 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 75
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 22 75 (accept_3_5 2 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 75
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 22 75)))))))))))))))))))))) (allB_succ 21 75 (allA_succ_of_accept 20 21 75
  (Polychromatic418967fa.accept_13_7_8_10_1_2663 20 21 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 75 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 21 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 75 3 6 7 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 75 (Polychromatic418967fa.accept_12_5_9_3_1_85 17 21 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 75
  (Polychromatic418967fa.accept_10_6_1_5_1_1024 16 21 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 21 75 3 5 7 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 21 75 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 21 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 75 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 21 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 21 75 3 4 7 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 21 75
  (Polychromatic418967fa.accept_12_11_9_3_1_792 11 21 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 75 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 21 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 75 3 3 7 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 75 (Polychromatic418967fa.accept_11_8_10_9_1_1401 8 21 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 75
  (Polychromatic418967fa.accept_12_7_9_3_1_767 7 21 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 21 75 3 2 7 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 21 75 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 21 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 75 (Polychromatic418967fa.accept_10_4_1_5_1_1018 4 21 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 21 75 3 1 7 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 21 75
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 21 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 21 75 (Polychromatic418967fa.accept_11_1_10_9_1_871 1 21 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 21 75))))))))))))))))))))) (allB_succ 20 75 (allA_succ_of_accept 19 20 75
  (accept_3_4 19 20 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 75
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 20 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 20 75 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 20 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 75 (accept_3_4 16 20 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 20 75 5 3 4 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 20 75 (Polychromatic418967fa.accept_9_5_2_3_1_194 14 20 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 75 (accept_3_4 13 20 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 75 (Polychromatic418967fa.accept_13_12_7_10_1_2662 12 20 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 20 75
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 20 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 20 75 5 2 4 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 20 75 (Polychromatic418967fa.accept_16_9_4_11_1_2661 9 20 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 75 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 20 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 75 (accept_3_4 7 20 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 75 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 20 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 20 75 5 1 4 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 20 75 (accept_3_4 4 20 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20 75 (Polychromatic418967fa.accept_13_3_7_10_1_668 3 20 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 20 75
  (Polychromatic418967fa.accept_19_2_1_18_1_2660 2 20 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 20 75 (accept_3_4 1 20 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20
  75)))))))))))))))))))) (allB_succ 19 75 (allA_succ_of_accept 18 19 75 (Polychromatic418967fa.accept_13_5_6_10_1_2659
  18 19 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 19 75 (accept_3_5 17 19
  75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 19 75 (Polychromatic418967fa.accept_6_4_1_3_1_77
  16 19 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 19 75
  (Polychromatic418967fa.accept_9_6_1_3_1_191 15 19 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 19 75 (accept_3_5 14 19 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 19
  75 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 19 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 19 75 (Polychromatic418967fa.accept_13_12_6_10_1_667 12 19 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 19 75 (accept_3_5 11 19 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 19 75 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 19 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 19 75 (Polychromatic418967fa.accept_12_9_7_3_1_1309 9
  19 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 75 (accept_3_5 8 19 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 75 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 19
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 75
  (Polychromatic418967fa.accept_9_6_1_3_1_191 6 19 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 75 (accept_3_5 5 19 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19 75
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 19 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 75 (Polychromatic418967fa.accept_13_3_6_10_1_2658 3 19 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 75 (accept_3_5 2 19 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 75 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 19 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 75))))))))))))))))))) (allB_succ 18 75 (allA_succ_of_accept 17
  18 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 18 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 18 75 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 18 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 18 75 3 5 6 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 18 75 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 18 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 18 75
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 18 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 18 75 3 4 6 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 18 75 (Polychromatic418967fa.accept_17_11_1_7_1_2657 11 18 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 75 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 18 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 18 75 3 3 6 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 18 75
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 18 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 75 (Polychromatic418967fa.accept_10_7_8_5_1_1008 7 18 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 75 3 2 6 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 18 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 75
  (Polychromatic418967fa.accept_12_4_6_3_1_332 4 18 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 18 75 3 1 6 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 18 75 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 18 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 18 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 75)))))))))))))))))) (allB_succ 17 75
  (allA_succ_of_accept 16 17 75 (accept_3_4 16 17 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17
  75 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 17 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 17 75 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 17 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 75 (accept_3_4 13 17 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 17 75 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 17 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 75 (Polychromatic418967fa.accept_9_2_8_3_1_181 11
  17 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 75 (accept_3_4 10 17 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 75 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 17
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 75
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 17 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 75 (accept_3_4 7 17 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17 75
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 17 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 75 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 17 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 75 (accept_3_4 4 17 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 75 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 17 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 75 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 17
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 75 (accept_3_4 1 17 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 75))))))))))))))))) (allB_succ 16 75 (allA_succ_of_accept 15 16
  75 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 16 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 16 75 (accept_3_5 14 16 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 16
  75 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 16 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 16 75 (Polychromatic418967fa.accept_23_12_16_6_1_2656 12 16 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 16 75 (accept_3_5 11 16 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 16 75 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 16 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 16 75 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9
  16 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 16 75 (accept_3_5 8 16 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 16 75 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 16
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 16 75
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 16 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 16 75 (accept_3_5 5 16 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 16 75
  (Polychromatic418967fa.accept_7_4_2_5_1_527 4 16 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 16 75 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 16 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 75 (accept_3_5 2 16 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 16 75 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 16 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 75)))))))))))))))) (allB_succ 15 75 (allA_succ_of_accept 14 15
  75 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 15 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 75 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 15 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 75 3 4 5 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 75 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 15 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 15 75 5 2 3 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 15 75 3 3 5 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 15 75
  (Polychromatic418967fa.accept_9_8_6_3_1_457 8 15 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 75 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 15 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 15 75 3 2 5 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 15 75 5 1 3 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 15 75 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 15 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 75 3 1 5 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 75
  (Polychromatic418967fa.accept_9_2_6_3_1_178 2 15 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 75 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 15 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 15 75))))))))))))))) (allB_succ 14 75 (allA_succ_of_accept 13 14 75
  (accept_3_4 13 14 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 75
  (Polychromatic418967fa.accept_18_12_14_3_1_2655 12 14 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 14 75 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 14 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 75 (accept_3_4 10 14 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 14 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 14 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 14 75 (Polychromatic418967fa.accept_9_8_5_3_1_777 8 14
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 75 (accept_3_4 7 14 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 14 75 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 14
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 75
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 14 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 14 75 (accept_3_4 4 14 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14 75
  (Polychromatic418967fa.accept_16_3_14_11_1_2654 3 14 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 14 75 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 14 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 75 (accept_3_4 1 14 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 75)))))))))))))) (allB_succ 13 75 (allA_succ_of_accept 12 13 75
  (Polychromatic418967fa.accept_10_2_3_5_1_996 12 13 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 75 (accept_3_5 11 13 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 13
  75 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 13 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 13 75 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 13 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 75 (accept_3_5 8 13 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 13 75 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 13 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 75 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 13
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 13 75 (accept_3_5 5 13 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13 75 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 13
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 13 75
  (Polychromatic418967fa.accept_21_3_13_12_1_2653 3 13 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 13 75 (accept_3_5 2 13 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 75
  (Polychromatic418967fa.accept_7_1_6_5_1_39 1 13 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 13 75))))))))))))) (allB_succ 12 75 (allA_succ_of_accept 11 12 75
  (Polychromatic418967fa.accept_13_11_12_10_1_2652 11 12 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 12 75 (Polychromatic418967fa.accept_11_10_1_9_1_2060 10 12 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 12 75 3 3 4 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 12 75 (Polychromatic418967fa.accept_10_8_2_5_1_596 8 12 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 75
  (Polychromatic418967fa.accept_8_7_4_3_1_156 7 12 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 12 75 3 2 4 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 12 75 (Polychromatic418967fa.accept_17_5_12_7_1_2651 5 12 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 75 (Polychromatic418967fa.accept_16_4_12_11_1_2650 4 12 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 12 75 3 1 4 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 12 75
  (Polychromatic418967fa.accept_13_2_12_10_1_2649 2 12 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 12 75 (Polychromatic418967fa.accept_16_1_12_11_1_2648 1 12 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 12 75)))))))))))) (allB_succ 11 75 (allA_succ_of_accept 10 11 75 (accept_3_4
  10 11 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 75
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 11 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 75 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 11 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 75 (accept_3_4 7 11 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 75 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 11 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 75 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 11
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 75 (accept_3_4 4 11 75
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 75 (Polychromatic418967fa.accept_13_3_11_10_1_2647
  3 11 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 75
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 11 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 75 (accept_3_4 1 11 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11 75)))))))))))
  (allB_succ 10 75 (allA_succ_of_accept 9 10 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 10 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 10 75 (accept_3_5 8 10 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 10 75 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 10 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 10 75 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 10
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 10 75 5 1 2 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 10 75
  (Polychromatic418967fa.accept_9_4_1_3_1_190 4 10 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 10 75 (Polychromatic418967fa.accept_17_3_10_7_1_2646 3 10 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 75 (accept_3_5 2 10 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 10 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 10 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 75)))))))))) (allB_succ 9 75 (allA_succ_of_accept 8 9 75
  (Polychromatic418967fa.accept_18_8_9_3_1_2645 8 9 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 9 75 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 9 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 75 3 2 3 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 75 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 9 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 75
  (Polychromatic418967fa.accept_7_4_2_5_1_527 4 9 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 9 75 3 1 3 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 9 75 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 9 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 75 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 9 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 75))))))))) (allB_succ 8 75 (allA_succ_of_accept 7 8
  75 (accept_3_4 7 8 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 75
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 8 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 8 75 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 8 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 8 75 (accept_3_4 4 8 75 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 8 75 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 8 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 2 8 75 (Polychromatic418967fa.accept_9_2_8_3_1_181 2 8 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 75 (accept_3_4 1 8 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 8 75)))))))) (allB_succ 7 75 (allA_succ_of_accept 6 7 75
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 7 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 75 (accept_3_5 5 7 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 75
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 7 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 75 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 7 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 75 (accept_3_5 2 7 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 75 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 7 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 7 75))))))) (allB_succ 6 75 (allA_succ_of_accept 5 6 75
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 6 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 75 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 6 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 3 6 75 3 1 2 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 2 6 75 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 6 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 75 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 6 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 75)))))) (allB_succ 5 75 (allA_succ_of_accept
  4 5 75 (accept_3_4 4 5 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 75
  (Polychromatic418967fa.accept_20_3_5_15_1_2644 3 5 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 5 75 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 5 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 75 (accept_3_4 1 5 75 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one
  5 75))))) (allB_succ 4 75 (allA_succ_of_accept 3 4 75 (Polychromatic418967fa.accept_17_3_4_7_1_1658 3 4 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 4 75 (accept_3_5 2 4 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 75 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 4 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 4 75)))) (allB_succ 3 75 (allA_succ_of_accept 2 3 75
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 3 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 75 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 3 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 3 75))) (allB_succ 2 75 (allA_succ_of_accept 1 2 75 (accept_3_4 1 2 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 2 75)) (allB_two
  75)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


