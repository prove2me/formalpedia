-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch106
-- name    : Polychromatic418967fa_Branch106
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:10:41.522329+00:00
-- url     : https://prove2.me/theorems/737d1b67-3d0c-4dee-95d6-e22d741adb0b
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

def Polychromatic418967fa.branch_106 : allB 106 106 :=
  allB_succ' 2 105 106 (Eq.refl Bool.true) (allA_succ_of_accept 1 105 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  105 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105 106)) (allB_succ' 3 104 106
  (Eq.refl Bool.true) (allA_of_3_1 3 104 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 103 106 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 103 106 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 103 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 103 106 (accept_3_3 2 103 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 103 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 103 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 103 106)))) (allB_succ' 5 102 106 (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 102 106 2 2 51 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 102 106 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 102 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 102 106 2 1 51 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 106 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 102 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102 106))))) (allB_succ' 6 101 106 (Eq.refl
  Bool.true) (allA_of_3_1 6 101 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 100 106 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 100 106 2 3 50 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 100 106 (accept_3_3 5 100 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 100
  106 2 2 50 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  100 106 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 100 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 100 106 2 1 50 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 100 106 (Polychromatic418967fa.accept_12_1_4_10_1_209 1 100 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100 106))))))) (allB_succ' 8 99 106 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 99 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 99 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99 106 (Polychromatic418967fa.accept_12_6_3_10_1_224 6 99 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 106 (accept_3_3 5 99 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 106 (Polychromatic418967fa.accept_22_4_11_18_1_1892
  4 99 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 106
  (Polychromatic418967fa.accept_10_3_9_6_1_94 3 99 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 99 106 (accept_3_3 2 99 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99
  106 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 99 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 99 106)))))))) (allB_succ' 9 98 106 (Eq.refl Bool.true) (allA_of_3_1 9 98 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 10 97 106 (Eq.refl Bool.true) (allA_succ_of_accept 9 97 106
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 97 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 97 106 (accept_3_3 8 97 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 97
  106 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 97 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 97 106 (Polychromatic418967fa.accept_15_6_7_1_1_93 6 97 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 97 106 (accept_3_3 5 97 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 97 106 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 97 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 97 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 97
  106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 106 (accept_3_3 2 97 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 97 106 (Polychromatic418967fa.accept_10_1_7_6_1_91 1
  97 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97 106)))))))))) (allB_succ' 11 96 106
  (Eq.refl Bool.true) (allA_succ_of_gcd 10 96 106 2 5 48 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 96 106 (Polychromatic418967fa.accept_13_9_5_2_1_2185 9 96 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 96 106 2 4 48 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 96 106
  (Polychromatic418967fa.accept_13_7_5_2_1_401 7 96 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 96 106 2 3 48 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 96 106 (accept_3_3 5 96 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 106
  2 2 48 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 96
  106 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 96 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 96 106 2 1 48 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 96 106 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 96 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 96 106))))))))))) (allB_succ' 12 95 106 (Eq.refl Bool.true) (allA_of_3_1 12
  95 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 94 106 (Eq.refl Bool.true) (allA_succ_of_gcd 12 94 106
  2 6 47 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 94
  106 (accept_3_3 11 94 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 94 106 2 5 47 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 94 106
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 94 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 94 106 2 4 47 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 94 106 (Polychromatic418967fa.accept_16_7_14_10_1_3544 7 94 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 94 106 2 3 47 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 94 106 (accept_3_3 5 94 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 94 106 2 2 47 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 94 106 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 94 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 94 106 2 1 47 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 94 106 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 94
  106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94 106))))))))))))) (allB_succ' 14 93 106
  (Eq.refl Bool.true) (allA_succ_of_accept 13 93 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 93 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 93 106
  (Polychromatic418967fa.accept_16_12_13_10_1_2637 12 93 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 93 106 (accept_3_3 11 93 106 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 93 106 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 93 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 106 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 93 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 106 (accept_3_3 8 93 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 93
  106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93 106
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 93 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 106 (accept_3_3 5 93 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93
  106 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 93 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 93 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 93 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 106 (accept_3_3 2 93 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 93 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 93 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93 106)))))))))))))) (allB_succ' 15 92 106 (Eq.refl Bool.true)
  (allA_of_3_1 15 92 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 91 106 (Eq.refl Bool.true)
  (allA_succ_of_accept 15 91 106 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 91 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 91 106 (accept_3_3 14 91 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 91 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 91 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 106 (Polychromatic418967fa.accept_9_3_1_7_1_97 12
  91 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 106 (accept_3_3 11 91
  106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 106
  (Polychromatic418967fa.accept_11_10_3_7_1_2564 10 91 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 91 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 91 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 106 (accept_3_3 8 91 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 91 106 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 91 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 106 (Polychromatic418967fa.accept_9_6_1_7_1_577 6
  91 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 106 (accept_3_3 5 91 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91 106 (Polychromatic418967fa.accept_9_4_1_7_1_293 4
  91 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 106
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 91 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 91 106 (accept_3_3 2 91 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91
  106 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 91 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 91 106)))))))))))))))) (allB_succ' 17 90 106 (Eq.refl Bool.true) (allA_succ_of_gcd 16 90 106 2 8 45 53
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 90 106
  (Polychromatic418967fa.accept_12_3_6_10_1_576 15 90 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 90 106 2 7 45 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 90 106 (Polychromatic418967fa.accept_22_13_2_18_1_4747 13 90 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 106 2 6 45 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 106 (accept_3_3 11 90 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 90 106 2 5 45 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 90 106 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 90 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 90 106 2 4 45 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 106 (Polychromatic418967fa.accept_14_7_6_8_1_2856 7
  90 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 106 2 3 45 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90 106 (accept_3_3 5 90
  106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 90 106 2 2 45 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 90 106
  (Polychromatic418967fa.accept_12_3_6_10_1_576 3 90 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 90 106 2 1 45 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 90 106 (Polychromatic418967fa.accept_13_1_12_2_1_384 1 90 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 90 106))))))))))))))))) (allB_succ' 18 89 106 (Eq.refl Bool.true)
  (allA_of_3_1 18 89 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 88 106 (Eq.refl Bool.true)
  (allA_succ_of_gcd 18 88 106 2 9 44 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 88 106 (accept_3_3 17 88 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 88
  106 2 8 44 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  88 106 (Polychromatic418967fa.accept_23_15_19_14_1_4746 15 88 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 88 106 2 7 44 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 88 106 (Polychromatic418967fa.accept_10_3_8_6_1_326 13 88 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 88 106 2 6 44 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 88 106 (accept_3_3 11 88 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 88 106 2 5 44 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 88 106 (Polychromatic418967fa.accept_27_9_7_25_1_2944 9 88 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 88 106 2 4 44 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 88 106
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 88 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 88 106 2 3 44 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 88 106 (accept_3_3 5 88 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 88 106
  2 2 44 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 88
  106 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 88 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 88 106 2 1 44 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 88 106 (Polychromatic418967fa.accept_12_1_4_10_1_209 1 88 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 88 106))))))))))))))))))) (allB_succ' 20 87 106 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 87 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 87 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 87 106 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 87 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 106 (accept_3_3 17 87 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 106 (Polychromatic418967fa.accept_7_2_3_1_1_10 16
  87 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 106
  (Polychromatic418967fa.accept_17_15_2_4_1_2423 15 87 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 87 106 (accept_3_3 14 87 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  87 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 87 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 87 106 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 87 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 106 (accept_3_3 11 87 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 106 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 87 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 106
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 87 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 106 (accept_3_3 8 87 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87
  106 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 87 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 87 106 (Polychromatic418967fa.accept_12_6_3_10_1_224 6 87 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 106 (accept_3_3 5 87 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 87 106 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 87 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 106 (Polychromatic418967fa.accept_9_3_6_7_1_562 3
  87 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 106 (accept_3_3 2 87 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 87
  106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87 106)))))))))))))))))))) (allB_succ' 21
  86 106 (Eq.refl Bool.true) (allA_of_3_1 21 86 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 85 106
  (Eq.refl Bool.true) (allA_succ_of_accept 21 85 106 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 85 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 106 (accept_3_3 20 85 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 85 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 106
  (Polychromatic418967fa.accept_13_5_7_2_1_852 18 85 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 85 106 (accept_3_3 17 85 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  85 106 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 85 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 85 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 85 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 106 (accept_3_3 14 85 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 106 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 85 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 106
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 85 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 106 (accept_3_3 11 85 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  85 106 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 85 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 85 106 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 85 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 106 (accept_3_3 8 85 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 85 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 106
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 85 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 106 (accept_3_3 5 85 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  106 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 85 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 85 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 85 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 106 (accept_3_3 2 85 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 106 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 85 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85 106)))))))))))))))))))))) (allB_succ' 23 84 106 (Eq.refl
  Bool.true) (allA_succ_of_gcd 22 84 106 2 11 42 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 84 106 (Polychromatic418967fa.accept_13_8_6_2_1_865 21 84 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 84 106 2 10 42 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 84 106
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 84 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 84 106 2 9 42 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 84 106 (accept_3_3 17 84 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 84
  106 2 8 42 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  84 106 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 84 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 84 106 2 7 42 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 84 106 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 84 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 106 2 6 42 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 106 (accept_3_3 11 84 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 106 2 5 42 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 84 106 (Polychromatic418967fa.accept_13_9_6_2_1_2200 9 84 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 84 106 2 4 42 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 84 106
  (Polychromatic418967fa.accept_15_7_9_1_1_473 7 84 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 84 106 2 3 42 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 84 106 (accept_3_3 5 84 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 84 106
  2 2 42 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 84
  106 (Polychromatic418967fa.accept_17_3_16_4_1_2416 3 84 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 84 106 2 1 42 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 84 106 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 84 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84 106))))))))))))))))))))))) (allB_succ' 24 83 106 (Eq.refl
  Bool.true) (allA_of_3_1 24 83 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 82 106 (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 82 106 2 12 41 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 82 106 (accept_3_3 23 82 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 82
  106 2 11 41 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  82 106 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 82 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 82 106 2 10 41 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 82 106 (Polychromatic418967fa.accept_13_6_4_2_1_1433 19 82 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 82 106 2 9 41 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 82 106 (accept_3_3 17 82 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 82 106 2 8 41 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 82 106 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 82 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 82 106 2 7 41 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 82 106
  (Polychromatic418967fa.accept_7_6_5_1_1_416 13 82 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 82 106 2 6 41 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 82 106 (accept_3_3 11 82 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 82
  106 2 5 41 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  82 106 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 82 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 82 106 2 4 41 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 82 106 (Polychromatic418967fa.accept_17_7_14_4_1_4745 7 82 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 82 106 2 3 41 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 82 106 (accept_3_3 5 82 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 82 106 2 2 41 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 82 106 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 82 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 82 106 2 1 41 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 82 106
  (Polychromatic418967fa.accept_10_1_2_6_1_638 1 82 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 82 106))))))))))))))))))))))))) (allB_succ' 26 81 106 (Eq.refl Bool.true) (allA_succ_of_accept 25 81 106
  (Polychromatic418967fa.accept_6_1_3_4_1_1 25 81 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 81 106 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 81 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 106 (accept_3_3 23 81 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 81 106 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 81 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 106
  (Polychromatic418967fa.accept_22_21_15_18_1_4744 21 81 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 81 106 (accept_3_3 20 81 106 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 81 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 81 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 106 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 81 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 106 (accept_3_3 17 81 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 106
  (Polychromatic418967fa.accept_19_16_5_11_1_4743 16 81 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 81 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 81 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 81 106 (accept_3_3 14 81 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 81 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 81 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 106 (Polychromatic418967fa.accept_7_5_4_1_1_412 12
  81 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 106 (accept_3_3 11 81
  106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 106 (Polychromatic418967fa.accept_7_3_4_1_1_71
  10 81 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 106
  (Polychromatic418967fa.accept_13_9_3_2_1_399 9 81 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 106 (accept_3_3 8 81 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81
  106 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 81 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 81 106 (Polychromatic418967fa.accept_12_6_9_10_1_565 6 81 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 106 (accept_3_3 5 81 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 81 106 (Polychromatic418967fa.accept_14_4_11_8_1_2034 4 81 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 81
  106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 106 (accept_3_3 2 81 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 81
  106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81 106))))))))))))))))))))))))))
  (allB_succ' 27 80 106 (Eq.refl Bool.true) (allA_of_3_1 27 80 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  28 79 106 (Eq.refl Bool.true) (allA_succ_of_accept 27 79 106 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 79 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 106 (accept_3_3 26 79 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 25
  79 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 106
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 79 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 106 (accept_3_3 23 79 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 106 (Polychromatic418967fa.accept_13_9_1_2_1_2952 22 79 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 79 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 106 (accept_3_3 20 79 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 106 (Polychromatic418967fa.accept_13_6_1_2_1_1464 19 79 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 106
  (Polychromatic418967fa.accept_15_3_4_1_1_1072 18 79 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 106 (accept_3_3 17 79 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 106 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 79 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 106 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 79 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 106 (accept_3_3 14 79 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 79 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 106
  (Polychromatic418967fa.accept_13_12_1_2_1_845 12 79 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 106 (accept_3_3 11 79 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 106 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 79 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 79 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 106 (accept_3_3 8 79 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 106 (Polychromatic418967fa.accept_20_7_19_6_1_4742 7 79 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 106
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 79 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 106 (accept_3_3 5 79 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  106 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 79 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 79 106 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 79 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 106 (accept_3_3 2 79 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 79 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 79 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79 106)))))))))))))))))))))))))))) (allB_succ' 29 78 106
  (Eq.refl Bool.true) (allA_succ_of_gcd 28 78 106 2 14 39 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 78 106 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 78 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 78 106 2 13 39 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 78 106
  (Polychromatic418967fa.accept_38_25_2_30_1_4741 25 78 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 106 2 12 39 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 78 106 (accept_3_3 23 78 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78
  106 2 11 39 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  78 106 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 78 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 78 106 2 10 39 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 78 106 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 78 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 106 2 9 39 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 106 (accept_3_3 17 78 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 106 2 8 39 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 78 106 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 78 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 78 106 2 7 39 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 106
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 78 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 78 106 2 6 39 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 78 106 (accept_3_3 11 78 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 78
  106 2 5 39 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  78 106 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 78 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 78 106 2 4 39 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 78 106 (Polychromatic418967fa.accept_16_7_14_10_1_3544 7 78 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 106 2 3 39 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 106 (accept_3_3 5 78 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 106 2 2 39 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 78 106 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 78 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 78 106 2 1 39 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 106
  (Polychromatic418967fa.accept_9_1_6_7_1_285 1 78 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 78 106))))))))))))))))))))))))))))) (allB_succ' 30 77 106 (Eq.refl Bool.true) (allA_of_3_1 30 77 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 76 106 (Eq.refl Bool.true) (allA_succ_of_gcd 30 76 106 2 15 38
  53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 76 106
  (accept_3_3 29 76 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 76 106 2 14 38 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 76 106
  (Polychromatic418967fa.accept_16_11_12_10_1_3641 27 76 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 76 106 2 13 38 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 76 106 (Polychromatic418967fa.accept_11_3_10_7_1_129 25 76 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 76 106 2 12 38 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 76 106 (accept_3_3 23 76 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 76 106 2 11 38 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 76 106
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 76 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 76 106 2 10 38 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 76 106 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 76 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 76 106 2 9 38 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 76 106 (accept_3_3 17 76 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 76 106 2 8 38 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 76 106 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 76 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 76 106 2 7 38 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 76 106 (Polychromatic418967fa.accept_12_1_4_10_1_209
  13 76 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 76 106 2 6 38 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 76 106 (accept_3_3 11
  76 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 76 106 2 5 38 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 76 106
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 76 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 76 106 2 4 38 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 76 106 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 76 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 76 106 2 3 38 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 76 106 (accept_3_3 5 76 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 76 106 2 2 38 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 76 106 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 76 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 76 106 2 1 38 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 76 106 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 76
  106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76 106)))))))))))))))))))))))))))))))
  (allB_succ' 32 75 106 (Eq.refl Bool.true) (allA_succ_of_accept 31 75 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 31
  75 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 75 106
  (Polychromatic418967fa.accept_12_6_3_10_1_224 30 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 75 106 (accept_3_3 29 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  75 106 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 75 106 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 75 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 106 (accept_3_3 26 75 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 75 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 75 106
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 75 106 (accept_3_3 23 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  75 106 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 75 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 75 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 106 (accept_3_3 20 75 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 75 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 106
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 75 106 (accept_3_3 17 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  75 106 (Polychromatic418967fa.accept_11_5_9_7_1_411 16 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 75 106 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 75 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 106 (accept_3_3 14 75 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 75 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 75 106
  (Polychromatic418967fa.accept_13_12_10_2_1_1451 12 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 75 106 (accept_3_3 11 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  75 106 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 75 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 75 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 106 (accept_3_3 8 75 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 75 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 106
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 106 (accept_3_3 5 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75
  106 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 75 106 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 75 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 106 (accept_3_3 2 75 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 75 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 75 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75 106)))))))))))))))))))))))))))))))) (allB_succ' 33 74 106
  (Eq.refl Bool.true) (allA_of_3_1 33 74 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 73 106 (Eq.refl
  Bool.true) (allA_succ_of_accept 33 73 106 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 73 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 106 (accept_3_3 32 73 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 73 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 106
  (Polychromatic418967fa.accept_7_2_3_1_1_10 30 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 106 (accept_3_3 29 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 106 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 73 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 106 (accept_3_3 26 73 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 106 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 73 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 106
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 106 (accept_3_3 23 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 106 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 106 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 73 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 106 (accept_3_3 20 73 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 73 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 106
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 106 (accept_3_3 17 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 106 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 73 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 106 (accept_3_3 14 73 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 106 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 73 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 106
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 106 (accept_3_3 11 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 106 (Polychromatic418967fa.accept_13_10_8_2_1_3829 10 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 106 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 73 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 106 (accept_3_3 8 73 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 73 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 106
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 106 (accept_3_3 5 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  106 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 73 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 106 (accept_3_3 2 73 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 106 (Polychromatic418967fa.accept_16_1_9_10_1_4740 1 73 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73 106)))))))))))))))))))))))))))))))))) (allB_succ' 35 72 106
  (Eq.refl Bool.true) (allA_succ_of_gcd 34 72 106 2 17 36 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 72 106 (Polychromatic418967fa.accept_19_14_15_11_1_4739 33 72 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 72 106 2 16 36 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 72 106
  (Polychromatic418967fa.accept_7_3_2_1_1_225 31 72 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 72 106 2 15 36 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 72 106 (accept_3_3 29 72 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 72
  106 2 14 36 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  72 106 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 72 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 72 106 2 13 36 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 72 106 (Polychromatic418967fa.accept_19_6_15_11_1_4738 25 72 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 106 2 12 36 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 106 (accept_3_3 23 72 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72 106 2 11 36 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 72 106
  (Polychromatic418967fa.accept_10_1_2_6_1_638 21 72 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 72 106 2 10 36 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 72 106 (Polychromatic418967fa.accept_15_4_12_1_1_1081 19 72 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72 106 2 9 36 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 72 106 (accept_3_3 17 72 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 72 106 2 8 36 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 72 106 (Polychromatic418967fa.accept_14_1_2_8_1_655 15 72 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 106 2 7 36 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 106 (Polychromatic418967fa.accept_7_6_2_1_1_214 13
  72 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 106 2 6 36 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 106 (accept_3_3 11
  72 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 106 2 5 36 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 72 106
  (Polychromatic418967fa.accept_13_9_7_2_1_3869 9 72 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 72 106 2 4 36 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 72 106 (Polychromatic418967fa.accept_19_7_15_11_1_3420 7 72 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 106 2 3 36 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 106 (accept_3_3 5 72 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 72 106 2 2 36 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 72 106 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 72 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 106 2 1 36 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 106 (Polychromatic418967fa.accept_10_1_2_6_1_638 1
  72 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  106))))))))))))))))))))))))))))))))))) (allB_succ' 36 71 106 (Eq.refl Bool.true) (allA_of_3_1 36 71 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 70 106 (Eq.refl Bool.true) (allA_succ_of_gcd 36 70 106 2 18 35 53
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 70 106
  (accept_3_3 35 70 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 70 106 2 17 35 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 70 106
  (Polychromatic418967fa.accept_13_7_5_2_1_401 33 70 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 70 106 2 16 35 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 70 106 (Polychromatic418967fa.accept_19_12_13_11_1_453 31 70 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 70 106 2 15 35 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 70 106 (accept_3_3 29 70 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 70 106 2 14 35 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 70 106 (Polychromatic418967fa.accept_21_6_7_1_1_4737 27 70 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 70 106 2 13 35 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 70 106
  (Polychromatic418967fa.accept_11_3_4_7_1_114 25 70 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 70 106 2 12 35 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 70 106 (accept_3_3 23 70 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 70
  106 2 11 35 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  70 106 (Polychromatic418967fa.accept_15_6_10_1_1_3675 21 70 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 70 106 2 10 35 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 70 106 (Polychromatic418967fa.accept_11_8_4_7_1_1303 19 70 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 70 106 2 9 35 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 70 106 (accept_3_3 17 70 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 70 106 2 8 35 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 70 106 (Polychromatic418967fa.accept_17_15_2_4_1_2423 15 70 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 70 106 2 7 35 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 70 106
  (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 70 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 70 106 2 6 35 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 70 106 (accept_3_3 11 70 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70
  106 2 5 35 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  70 106 (Polychromatic418967fa.accept_13_9_5_2_1_2185 9 70 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 70 106 2 4 35 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 70 106 (Polychromatic418967fa.accept_13_7_5_2_1_401 7 70 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 70 106 2 3 35 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 70 106 (accept_3_3 5 70 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 70 106 2 2 35 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 70 106 (Polychromatic418967fa.accept_11_3_4_7_1_114 3 70 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 70 106 2 1 35 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 70 106
  (Polychromatic418967fa.accept_25_1_20_6_1_4736 1 70 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 70 106))))))))))))))))))))))))))))))))))))) (allB_succ' 38 69 106 (Eq.refl Bool.true) (allA_succ_of_accept
  37 69 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 69 106 (Polychromatic418967fa.accept_15_6_9_1_1_1823 36 69 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 106 (accept_3_3 35 69 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 106 (Polychromatic418967fa.accept_20_14_9_6_1_3346 34 69 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 106
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 69 106 (accept_3_3 32 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  69 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 69 106 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 69 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 106 (accept_3_3 29 69 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 106 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 69 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 106
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 69 106 (accept_3_3 26 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  69 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 69 106 (Polychromatic418967fa.accept_13_11_4_2_1_2954 24 69 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 106 (accept_3_3 23 69 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 106 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 69 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 106
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 69 106 (accept_3_3 20 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  69 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 69 106 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 69 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 106 (accept_3_3 17 69 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 106 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 69 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 106
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 69 106 (accept_3_3 14 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  69 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 69 106 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 69 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 106 (accept_3_3 11 69 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 106 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 69 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 106
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 69 106 (accept_3_3 8 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69
  106 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 69 106 (Polychromatic418967fa.accept_12_6_9_10_1_565 6 69 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 106 (accept_3_3 5 69 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 69 106 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 69 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 69
  106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 106 (accept_3_3 2 69 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 69
  106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  106)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 68 106 (Eq.refl Bool.true) (allA_of_3_1 39 68 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 40 67 106 (Eq.refl Bool.true) (allA_succ_of_accept 39 67 106
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 67 106 (accept_3_3 38 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  67 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 67 106 (Polychromatic418967fa.accept_15_6_7_1_1_93 36 67 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 67 106 (accept_3_3 35 67 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 67 106 (Polychromatic418967fa.accept_19_15_10_11_1_4735 34 67 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 67 106
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 67 106 (accept_3_3 32 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  67 106 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 67 106 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 67 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 67 106 (accept_3_3 29 67 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 67 106 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 67 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 67 106
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 67 106 (accept_3_3 26 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  67 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 67 106 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 67 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 67 106 (accept_3_3 23 67 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 67 106 (Polychromatic418967fa.accept_17_5_16_4_1_4734 22 67 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 67 106
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 67 106 (accept_3_3 20 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  67 106 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 67 106 (Polychromatic418967fa.accept_14_4_11_8_1_2034 18 67 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 67 106 (accept_3_3 17 67 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 67 106 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 67 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 67 106
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 67 106 (accept_3_3 14 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  67 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 67 106 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 67 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 67 106 (accept_3_3 11 67 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 67 106 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 67 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 67 106
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 67 106 (accept_3_3 8 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 67
  106 (Polychromatic418967fa.accept_16_7_3_10_1_3614 7 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 67 106 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 67 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 67 106 (accept_3_3 5 67 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 67 106 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 67 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 67 106
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 67 106 (accept_3_3 2 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 67
  106 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 67 106)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 66 106 (Eq.refl Bool.true) (allA_succ_of_gcd
  40 66 106 2 20 33 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 66 106 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 66 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 66 106 2 19 33 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 66 106 (Polychromatic418967fa.accept_7_2_3_1_1_10 37
  66 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66 106 2 18 33 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 66 106 (accept_3_3 35
  66 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66 106 2 17 33 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 66 106
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 66 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 66 106 2 16 33 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 66 106 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 66 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 106 2 15 33 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 106 (accept_3_3 29 66 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66 106 2 14 33 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 66 106 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 66 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 66 106 2 13 33 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 66 106
  (Polychromatic418967fa.accept_7_4_3_1_1_87 25 66 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 66 106 2 12 33 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 66 106 (accept_3_3 23 66 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66
  106 2 11 33 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  66 106 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 66 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 66 106 2 10 33 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 66 106 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 66 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 106 2 9 33 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 106 (accept_3_3 17 66 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66 106 2 8 33 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 66 106 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 66 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 66 106 2 7 33 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 106
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 66 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 66 106 2 6 33 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 66 106 (accept_3_3 11 66 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66
  106 2 5 33 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  66 106 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 66 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 66 106 2 4 33 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 66 106 (Polychromatic418967fa.accept_15_7_6_1_1_1091 7 66 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 106 2 3 33 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 106 (accept_3_3 5 66 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 106 2 2 33 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 66 106 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 66 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 66 106 2 1 33 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 106
  (Polychromatic418967fa.accept_9_1_3_7_1_6 1 66 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 66 106))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 65 106 (Eq.refl Bool.true) (allA_of_3_1 42 65
  106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 64 106 (Eq.refl Bool.true) (allA_succ_of_gcd 42 64 106 2
  21 32 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 64
  106 (accept_3_3 41 64 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 64 106 2 20 32 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 64 106
  (Polychromatic418967fa.accept_9_3_1_7_1_97 39 64 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 64 106 2 19 32 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 64 106 (Polychromatic418967fa.accept_12_1_4_10_1_209 37 64 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 64 106 2 18 32 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 64 106 (accept_3_3 35 64 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 64 106 2 17 32 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 64 106 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 64 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 64 106 2 16 32 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 64 106
  (Polychromatic418967fa.accept_9_4_1_7_1_293 31 64 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 64 106 2 15 32 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 64 106 (accept_3_3 29 64 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 64
  106 2 14 32 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  64 106 (Polychromatic418967fa.accept_11_5_9_7_1_411 27 64 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 64 106 2 13 32 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 64 106 (Polychromatic418967fa.accept_10_5_4_6_1_319 25 64 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 64 106 2 12 32 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 64 106 (accept_3_3 23 64 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 64 106 2 11 32 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 64 106
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 64 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 64 106 2 10 32 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 64 106 (Polychromatic418967fa.accept_12_7_4_10_1_572 19 64 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 64 106 2 9 32 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 64 106 (accept_3_3 17 64 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 64 106 2 8 32 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 64 106 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 64 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 64 106 2 7 32 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 64 106 (Polychromatic418967fa.accept_9_4_1_7_1_293 13
  64 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 64 106 2 6 32 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 64 106 (accept_3_3 11
  64 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64 106 2 5 32 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 64 106
  (Polychromatic418967fa.accept_17_9_13_4_1_2408 9 64 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 64 106 2 4 32 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 64 106 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 64 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 64 106 2 3 32 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 64 106 (accept_3_3 5 64 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 64 106 2 2 32 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 64 106 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 64 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 64 106 2 1 32 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 64 106 (Polychromatic418967fa.accept_12_1_4_10_1_209 1
  64 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  106))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 63 106 (Eq.refl Bool.true) (allA_succ_of_accept 43 63
  106 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 63 106 (Polychromatic418967fa.accept_12_6_3_10_1_224 42 63 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 63 106 (accept_3_3 41 63 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 63 106 (Polychromatic418967fa.accept_24_16_15_10_1_4733 40 63 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 106
  (Polychromatic418967fa.accept_10_9_3_6_1_686 39 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 63 106 (accept_3_3 38 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  63 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 63 106 (Polychromatic418967fa.accept_13_10_11_2_1_3862 36 63 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 106 (accept_3_3 35 63 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 106 (Polychromatic418967fa.accept_14_6_7_8_1_624 34 63 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 106
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 63 106 (accept_3_3 32 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  63 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 63 106 (Polychromatic418967fa.accept_12_6_3_10_1_224 30 63 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 106 (accept_3_3 29 63 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 106 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 63 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 106
  (Polychromatic418967fa.accept_10_7_3_6_1_644 27 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 63 106 (accept_3_3 26 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  63 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 63 106 (Polychromatic418967fa.accept_17_7_12_4_1_2524 24 63 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 106 (accept_3_3 23 63 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 106 (Polychromatic418967fa.accept_13_9_11_2_1_1491 22 63
  106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 106
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 63 106 (accept_3_3 20 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  63 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 63 106 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 63 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 106 (accept_3_3 17 63 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 106 (Polychromatic418967fa.accept_13_3_11_2_1_1422 16 63 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 106
  (Polychromatic418967fa.accept_11_4_8_7_1_819 15 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 63 106 (accept_3_3 14 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  63 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 63 106 (Polychromatic418967fa.accept_18_12_9_16_1_4732 12 63 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 106 (accept_3_3 11 63 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 106 (Polychromatic418967fa.accept_13_10_11_2_1_3862 10 63
  106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 106
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 106 (accept_3_3 8 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63
  106 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 63 106 (Polychromatic418967fa.accept_12_6_3_10_1_224 6 63 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 106 (accept_3_3 5 63 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 63 106 (Polychromatic418967fa.accept_11_4_8_7_1_819 4 63 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 106 (Polychromatic418967fa.accept_13_3_11_2_1_1422
  3 63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 106 (accept_3_3 2 63
  106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 1
  63 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  106)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 62 106 (Eq.refl Bool.true) (allA_of_3_1 45 62 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 46 61 106 (Eq.refl Bool.true) (allA_succ_of_accept 45 61 106
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 61 106 (accept_3_3 44 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  61 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 61 106 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 61 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 61 106 (accept_3_3 41 61 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 61 106 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 61 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 61 106
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 61 106 (accept_3_3 38 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  61 106 (Polychromatic418967fa.accept_10_7_1_6_1_673 37 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 61 106 (Polychromatic418967fa.accept_19_17_4_11_1_4731 36 61 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 61 106 (accept_3_3 35 61 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 61 106 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 61 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 61 106
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 61 106 (accept_3_3 32 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  61 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 61 106 (Polychromatic418967fa.accept_16_14_13_10_1_2624 30 61 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 61 106 (accept_3_3 29 61 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 61 106 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 61 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 61 106
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 61 106 (accept_3_3 26 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  61 106 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 61 106 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 61 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 61 106 (accept_3_3 23 61 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 61 106 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 61 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 61 106
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 61 106 (accept_3_3 20 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  61 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 61 106 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 61 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 61 106 (accept_3_3 17 61 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 61 106 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 61 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 61 106
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 61 106 (accept_3_3 14 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  61 106 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 61 106 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 61 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 61 106 (accept_3_3 11 61 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 61 106 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 61 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 61 106
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 61 106 (accept_3_3 8 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 61
  106 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 61 106 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 61 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 61 106 (accept_3_3 5 61 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 61 106 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 61 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 61 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 61
  106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 106 (accept_3_3 2 61 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 61 106 (Polychromatic418967fa.accept_11_1_6_7_1_116 1
  61 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61
  106)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 60 106 (Eq.refl Bool.true) (allA_succ_of_gcd 46 60
  106 2 23 30 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  60 106 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 60 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 60 106 2 22 30 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 60 106 (Polychromatic418967fa.accept_16_11_12_10_1_3641 43 60 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 106 2 21 30 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 106 (accept_3_3 41 60 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60 106 2 20 30 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 60 106
  (Polychromatic418967fa.accept_9_3_6_7_1_562 39 60 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 60 106 2 19 30 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 60 106 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 60 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 106 2 18 30 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 106 (accept_3_3 35 60 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 106 2 17 30 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 106 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 60 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 60 106 2 16 30 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 60 106
  (Polychromatic418967fa.accept_7_3_4_1_1_71 31 60 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 60 106 2 15 30 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 60 106 (accept_3_3 29 60 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60
  106 2 14 30 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  60 106 (Polychromatic418967fa.accept_16_11_12_10_1_3641 27 60 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 60 106 2 13 30 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 60 106 (Polychromatic418967fa.accept_14_11_4_8_1_664 25 60 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 106 2 12 30 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 106 (accept_3_3 23 60 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 106 2 11 30 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 60 106
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 60 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 60 106 2 10 30 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 60 106 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 60 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 106 2 9 30 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 106 (accept_3_3 17 60 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 60 106 2 8 30 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 60 106 (Polychromatic418967fa.accept_18_15_6_16_1_4730 15 60 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 60 106 2 7 30 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 106
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 60 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 60 106 2 6 30 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 60 106 (accept_3_3 11 60 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60
  106 2 5 30 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  60 106 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 60 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 60 106 2 4 30 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 60 106 (Polychromatic418967fa.accept_13_7_8_2_1_1483 7 60 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 106 2 3 30 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 106 (accept_3_3 5 60 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 106 2 2 30 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 60 106 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 60 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 60 106 2 1 30 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 106
  (Polychromatic418967fa.accept_9_1_6_7_1_285 1 60 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 60 106))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 59 106 (Eq.refl Bool.true) (allA_of_3_1
  48 59 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 58 106 (Eq.refl Bool.true) (allA_succ_of_gcd 48 58
  106 2 24 29 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  58 106 (accept_3_3 47 58 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 58 106 2 23 29 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 58 106
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 58 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 58 106 2 22 29 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 58 106 (Polychromatic418967fa.accept_10_3_8_6_1_326 43 58 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 58 106 2 21 29 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 58 106 (accept_3_3 41 58 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 58 106 2 20 29 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 58 106 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 58 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 58 106 2 19 29 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 58 106
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 58 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 58 106 2 18 29 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 58 106 (accept_3_3 35 58 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 58
  106 2 17 29 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  58 106 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 58 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 58 106 2 16 29 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 58 106 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 58 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 58 106 2 15 29 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 58 106 (accept_3_3 29 58 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 58 106 2 14 29 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 58 106
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 58 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 58 106 2 13 29 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 58 106 (Polychromatic418967fa.accept_13_12_6_2_1_1441 25 58 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 58 106 2 12 29 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 58 106 (accept_3_3 23 58 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 58 106 2 11 29 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 58 106 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 58 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 58 106 2 10 29 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 58 106
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 58 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 58 106 2 9 29 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 58 106 (accept_3_3 17 58 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 58
  106 2 8 29 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  58 106 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 58 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 58 106 2 7 29 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 58 106 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 58 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 58 106 2 6 29 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 58 106 (accept_3_3 11 58 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58 106 2 5 29 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 58 106 (Polychromatic418967fa.accept_13_9_6_2_1_2200 9 58 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 58 106 2 4 29 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 58 106
  (Polychromatic418967fa.accept_18_7_4_16_1_2299 7 58 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 58 106 2 3 29 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 58 106 (accept_3_3 5 58 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 58 106
  2 2 29 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 58
  106 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 58 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 58 106 2 1 29 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 58 106 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 58 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 58 106))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 57
  106 (Eq.refl Bool.true) (allA_succ_of_accept 49 57 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 57 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 57 106
  (Polychromatic418967fa.accept_13_9_5_2_1_2185 48 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 57 106 (accept_3_3 47 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  57 106 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 57 106 (Polychromatic418967fa.accept_17_11_6_4_1_4729 45 57 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 106 (accept_3_3 44 57 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 57 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 57 106
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 57 106 (accept_3_3 41 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  57 106 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 57 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 57 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 106 (accept_3_3 38 57 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 57 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 57 106
  (Polychromatic418967fa.accept_13_10_5_2_1_1477 36 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 57 106 (accept_3_3 35 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  57 106 (Polychromatic418967fa.accept_15_4_12_1_1_1081 34 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 57 106 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 57 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 106 (accept_3_3 32 57 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 57 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 57 106
  (Polychromatic418967fa.accept_12_6_9_10_1_565 30 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 57 106 (accept_3_3 29 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  57 106 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 57 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 57 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 106 (accept_3_3 26 57 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 57 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 57 106
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 57 106 (accept_3_3 23 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  57 106 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 57 106 (Polychromatic418967fa.accept_10_1_7_6_1_91 21 57 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 106 (accept_3_3 20 57 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 57 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 57 106
  (Polychromatic418967fa.accept_12_6_9_10_1_565 18 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 57 106 (accept_3_3 17 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  57 106 (Polychromatic418967fa.accept_13_3_5_2_1_1475 16 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 57 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 57 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 106 (accept_3_3 14 57 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 57 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 57 106
  (Polychromatic418967fa.accept_13_12_5_2_1_2173 12 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 57 106 (accept_3_3 11 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  57 106 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 57 106 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 57 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 106 (accept_3_3 8 57 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 57 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 106
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 106 (accept_3_3 5 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57
  106 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 57 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 57 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 57 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 106 (accept_3_3 2 57 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 57 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 57 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 106))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 51 56 106 (Eq.refl Bool.true) (allA_of_3_1 51 56 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  52 55 106 (Eq.refl Bool.true) (allA_succ_of_accept 51 55 106 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 55 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 106 (accept_3_3 50 55 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 49
  55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 55 106
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 55 106 (accept_3_3 47 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  55 106 (Polychromatic418967fa.accept_16_14_7_10_1_898 46 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 55 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 55 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 55 106 (accept_3_3 44 55 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 106 (Polychromatic418967fa.accept_15_13_10_1_1_1862 43 55 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 106
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 106 (accept_3_3 41 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  55 106 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 55 106 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 55 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 106 (accept_3_3 38 55 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 55 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 106
  (Polychromatic418967fa.accept_13_10_3_2_1_4728 36 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 55 106 (accept_3_3 35 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  55 106 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 55 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 55 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 106 (accept_3_3 32 55 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 106 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 55 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 106
  (Polychromatic418967fa.accept_7_2_6_1_1_73 30 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 55 106 (accept_3_3 29 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  55 106 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 55 106 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 55 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 106 (accept_3_3 26 55 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 55 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 106
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 55 106 (accept_3_3 23 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  55 106 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 55 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 55 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 106 (accept_3_3 20 55 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 106 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 55 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 106
  (Polychromatic418967fa.accept_13_5_3_2_1_1499 18 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 106 (accept_3_3 17 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  55 106 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 55 106 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 55 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 106 (accept_3_3 14 55 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 55 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 106
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 106 (accept_3_3 11 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  55 106 (Polychromatic418967fa.accept_13_10_3_2_1_4728 10 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 55 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 55 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 106 (accept_3_3 8 55 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 106 (Polychromatic418967fa.accept_14_7_13_8_1_2067 7 55 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 106
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 106 (accept_3_3 5 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55
  106 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 55 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 106 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 55 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 106 (accept_3_3 2 55 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 55 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 106))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 53 54 106 (Eq.refl Bool.true) (allA_succ_of_gcd 52 54 106 2 26 27 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 54 106
  (Polychromatic418967fa.accept_12_3_6_10_1_576 51 54 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 54 106 2 25 27 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 54 106 (Polychromatic418967fa.accept_20_9_14_6_1_320 49 54 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 106 2 24 27 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 106 (accept_3_3 47 54 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 106 2 23 27 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 54 106 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 54 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 54 106 2 22 27 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 54 106
  (Polychromatic418967fa.accept_19_5_16_11_1_4727 43 54 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 54 106 2 21 27 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 54 106 (accept_3_3 41 54 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 54
  106 2 20 27 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  54 106 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 54 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 54 106 2 19 27 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 54 106 (Polychromatic418967fa.accept_15_7_9_1_1_473 37 54 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 106 2 18 27 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 106 (accept_3_3 35 54 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 54 106 2 17 27 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 54 106
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 54 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 54 106 2 16 27 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 54 106 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 54 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 106 2 15 27 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 106 (accept_3_3 29 54 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 106 2 14 27 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54 106 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 54 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 54 106 2 13 27 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 54 106
  (Polychromatic418967fa.accept_7_4_5_1_1_418 25 54 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 106 2 12 27 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 54 106 (accept_3_3 23 54 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54
  106 2 11 27 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  54 106 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 54 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 54 106 2 10 27 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 54 106 (Polychromatic418967fa.accept_20_19_14_6_1_4726 19 54 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 106 2 9 27 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 106 (accept_3_3 17 54 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 106 2 8 27 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 54 106 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 54 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 54 106 2 7 27 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 106
  (Polychromatic418967fa.accept_7_6_5_1_1_416 13 54 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 54 106 2 6 27 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 54 106 (accept_3_3 11 54 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54
  106 2 5 27 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  54 106 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 54 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 54 106 2 4 27 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 54 106 (Polychromatic418967fa.accept_15_7_9_1_1_473 7 54 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 106 2 3 27 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 106 (accept_3_3 5 54 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 106 2 2 27 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 54 106 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 54 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 54 106 2 1 27 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 106
  (Polychromatic418967fa.accept_20_1_14_6_1_4725 1 54 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 54 106))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 106 (allA_of_3_1 53 53 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 52 106 (allA_succ_of_accept 51 52 106
  (Polychromatic418967fa.accept_7_2_3_1_1_10 51 52 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 52 106 2 25 26 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 52 106 (Polychromatic418967fa.accept_12_1_4_10_1_209 49 52 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 52 106 2 24 26 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 52 106 (accept_3_3 47 52 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 52 106 2 23 26 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 52 106 (Polychromatic418967fa.accept_19_7_14_11_1_4724 45 52
  106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 52 106 2 22 26 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 52 106
  (Polychromatic418967fa.accept_12_7_4_10_1_572 43 52 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 52 106 2 21 26 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 52 106 (accept_3_3 41 52 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 52
  106 2 20 26 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  52 106 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 52 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 52 106 2 19 26 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 52 106 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 52 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 52 106 2 18 26 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 52 106 (accept_3_3 35 52 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 52 106 2 17 26 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 52 106
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 52 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 52 106 2 16 26 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 52 106 (Polychromatic418967fa.accept_10_1_2_6_1_638 31 52 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 52 106 2 15 26 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 52 106 (accept_3_3 29 52 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 52 106 2 14 26 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 52 106 (Polychromatic418967fa.accept_20_7_12_6_1_2164 27 52 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 52 106 2 13 26 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 52 106
  (Polychromatic418967fa.accept_7_4_3_1_1_87 25 52 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 52 106 2 12 26 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 52 106 (accept_3_3 23 52 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 52
  106 2 11 26 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  52 106 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 52 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 52 106 2 10 26 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 52 106 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 52 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 52 106 2 9 26 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 52 106 (accept_3_3 17 52 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52 106 2 8 26 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 52 106 (Polychromatic418967fa.accept_11_4_8_7_1_819 15 52 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 52 106 2 7 26 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 52 106
  (Polychromatic418967fa.accept_12_1_4_10_1_209 13 52 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 52 106 2 6 26 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 52 106 (accept_3_3 11 52 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 52
  106 2 5 26 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  52 106 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 52 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 52 106 2 4 26 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 52 106 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 52 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 52 106 2 3 26 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 52 106 (accept_3_3 5 52 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 52 106 2 2 26 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 52 106 (Polychromatic418967fa.accept_19_3_14_11_1_2214 3 52 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 52 106 2 1 26 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 52 106
  (Polychromatic418967fa.accept_10_1_2_6_1_638 1 52 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 52 106)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 106 (allA_succ_of_accept 50 51 106
  (accept_3_3 50 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 106
  (Polychromatic418967fa.accept_4_1_3_2_1_3 49 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 51 106 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 51 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 106 (accept_3_3 47 51 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 51 106 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 51 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 45
  51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 106 (accept_3_3 44 51
  106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 106 (Polychromatic418967fa.accept_6_1_3_4_1_1
  43 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 51 106
  (Polychromatic418967fa.accept_10_2_1_6_1_634 42 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 51 106 (accept_3_3 41 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  51 106 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 51 106 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 51 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 106 (accept_3_3 38 51 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 51 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 51 106
  (Polychromatic418967fa.accept_13_10_12_2_1_1460 36 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 51 106 (accept_3_3 35 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  51 106 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 51 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 51 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 106 (accept_3_3 32 51 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 51 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 51 106
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 51 106 (accept_3_3 29 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  51 106 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 51 106 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 51 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 106 (accept_3_3 26 51 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 51 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 51 106
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 51 106 (accept_3_3 23 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  51 106 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 51 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 51 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 106 (accept_3_3 20 51 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 51 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 51 106
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 51 106 (accept_3_3 17 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  51 106 (Polychromatic418967fa.accept_13_3_12_2_1_385 16 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 51 106 (Polychromatic418967fa.accept_10_5_1_6_1_672 15 51 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 106 (accept_3_3 14 51 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 51 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 106
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 51 106 (accept_3_3 11 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  51 106 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 51 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 51 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 106 (accept_3_3 8 51 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 51 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 106
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 106 (accept_3_3 5 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51
  106 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 51 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 51 106 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 51 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 106 (accept_3_3 2 51 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 51 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 51 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 106)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 106 (allA_of_3_1 50 50 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 49 106
  (allA_succ_of_accept 48 49 106 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 49 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 106 (accept_3_3 47 49 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 49 106 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 49 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 106 (Polychromatic418967fa.accept_6_3_1_4_1_25 45
  49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 106 (accept_3_3 44 49
  106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 106 (Polychromatic418967fa.accept_4_3_1_2_1_62
  43 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 49 106
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 49 106 (accept_3_3 41 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  49 106 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 49 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 49 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 106 (accept_3_3 38 49 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 106 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 49 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 106
  (Polychromatic418967fa.accept_17_2_15_4_1_4723 36 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 49 106 (accept_3_3 35 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  49 106 (Polychromatic418967fa.accept_13_8_10_2_1_1450 34 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 49 106 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 49 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 106 (accept_3_3 32 49 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 49 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 106
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 106 (accept_3_3 29 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  49 106 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 49 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 49 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 106 (accept_3_3 26 49 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 106 (Polychromatic418967fa.accept_10_5_9_6_1_697 25 49 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 106
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 106 (accept_3_3 23 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  49 106 (Polychromatic418967fa.accept_25_22_24_6_1_4722 22 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 49 106 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 49 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 106 (accept_3_3 20 49 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 49 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 106
  (Polychromatic418967fa.accept_13_5_10_2_1_856 18 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 106 (accept_3_3 17 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  49 106 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 49 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 49 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 106 (accept_3_3 14 49 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 106 (Polychromatic418967fa.accept_10_3_9_6_1_94 13 49 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 106
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 49 106 (accept_3_3 11 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  49 106 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 49 106 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 49 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 106 (accept_3_3 8 49 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 49 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 106
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 106 (accept_3_3 5 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  106 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 49 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 49 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 49 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 106 (accept_3_3 2 49 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 106 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 49 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 106)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 48 106 (allA_succ_of_accept 47 48 106 (accept_3_3 47 48 106 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 48 106 2 23 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 48 106 (Polychromatic418967fa.accept_13_6_9_2_1_838 45 48 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 48 106 2 22 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 48 106 (Polychromatic418967fa.accept_10_3_8_6_1_326 43
  48 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 106 2 21 24 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 106 (accept_3_3 41
  48 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 106 2 20 24 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 48 106
  (Polychromatic418967fa.accept_19_1_10_11_1_4721 39 48 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 48 106 2 19 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 48 106 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 48 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 106 2 18 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 106 (accept_3_3 35 48 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48 106 2 17 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 48 106 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 48 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 48 106 2 16 24 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 48 106
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 48 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 48 106 2 15 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 48 106 (accept_3_3 29 48 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48
  106 2 14 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  48 106 (Polychromatic418967fa.accept_13_1_9_2_1_1448 27 48 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 48 106 2 13 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 48 106 (Polychromatic418967fa.accept_11_3_4_7_1_114 25 48 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 106 2 12 24 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 106 (accept_3_3 23 48 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 106 2 11 24 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 48 106
  (Polychromatic418967fa.accept_14_7_6_8_1_2856 21 48 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 48 106 2 10 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 48 106 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 48 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 106 2 9 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 106 (accept_3_3 17 48 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 48 106 2 8 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 48 106 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 48 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 48 106 2 7 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 106 (Polychromatic418967fa.accept_9_4_3_7_1_296 13
  48 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 106 2 6 24 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 106 (accept_3_3 11
  48 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 106 2 5 24 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 48 106
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 48 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 48 106 2 4 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 48 106 (Polychromatic418967fa.accept_13_7_9_2_1_2167 7 48 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 106 2 3 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 106 (accept_3_3 5 48 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 48 106 2 2 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 48 106 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 48 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 106 2 1 24 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 106 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 48
  106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48
  106)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 106 (allA_of_3_1 47 47 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 46 106 (allA_succ_of_accept 45 46 106 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 46
  106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 46 106 2 22 23 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 46 106
  (Polychromatic418967fa.accept_17_9_12_4_1_3468 43 46 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 46 106 2 21 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 46 106 (accept_3_3 41 46 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 46
  106 2 20 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  46 106 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 46 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 46 106 2 19 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 46 106 (Polychromatic418967fa.accept_16_5_14_10_1_3644 37 46 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 46 106 2 18 23 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 46 106 (accept_3_3 35 46 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 46 106 2 17 23 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 46 106
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 46 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 46 106 2 16 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 46 106 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 46 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 46 106 2 15 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 46 106 (accept_3_3 29 46 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 46 106 2 14 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 46 106 (Polychromatic418967fa.accept_22_5_2_18_1_4720 27 46 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 46 106 2 13 23 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 46 106
  (Polychromatic418967fa.accept_14_11_4_8_1_664 25 46 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 46 106 2 12 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 46 106 (accept_3_3 23 46 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 46
  106 2 11 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  46 106 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 46 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 46 106 2 10 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 46 106 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 46 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 46 106 2 9 23 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 46 106 (accept_3_3 17 46 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 46 106 2 8 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 46 106 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 46 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 46 106 2 7 23 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 46 106
  (Polychromatic418967fa.accept_9_4_1_7_1_293 13 46 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 46 106 2 6 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 46 106 (accept_3_3 11 46 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46
  106 2 5 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  46 106 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 46 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 46 106 2 4 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 46 106 (Polychromatic418967fa.accept_16_7_14_10_1_3544 7 46 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 46 106 2 3 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 46 106 (accept_3_3 5 46 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 46 106 2 2 23 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 46 106 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 46 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 46 106 2 1 23 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 46 106
  (Polychromatic418967fa.accept_18_1_10_16_1_566 1 46 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 46 106)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 106 (allA_succ_of_accept 44 45 106
  (accept_3_3 44 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 106
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 45 106 (Polychromatic418967fa.accept_12_6_9_10_1_565 42 45 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 106 (accept_3_3 41 45 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 45 106 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 45 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 39
  45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 106 (accept_3_3 38 45
  106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 106 (Polychromatic418967fa.accept_6_1_3_4_1_1
  37 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 106
  (Polychromatic418967fa.accept_13_10_6_2_1_1440 36 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 45 106 (accept_3_3 35 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  45 106 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 45 106 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 45 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 106 (accept_3_3 32 45 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 45 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 45 106
  (Polychromatic418967fa.accept_7_2_3_1_1_10 30 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 45 106 (accept_3_3 29 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  45 106 (Polychromatic418967fa.accept_11_6_1_7_1_1315 28 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 45 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 45 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 106 (accept_3_3 26 45 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 45 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 45 106
  (Polychromatic418967fa.accept_10_4_5_6_1_651 24 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 45 106 (accept_3_3 23 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  45 106 (Polychromatic418967fa.accept_13_9_6_2_1_2200 22 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 45 106 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 45 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 106 (accept_3_3 20 45 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 45 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 106
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 45 106 (accept_3_3 17 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  45 106 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 45 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 45 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 106 (accept_3_3 14 45 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 45 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 106
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 45 106 (accept_3_3 11 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  45 106 (Polychromatic418967fa.accept_13_10_6_2_1_1440 10 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 45 106 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 45 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 106 (accept_3_3 8 45 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 45 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 106
  (Polychromatic418967fa.accept_11_6_1_7_1_1315 6 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 106 (accept_3_3 5 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45
  106 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 45 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 45 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 45 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 106 (accept_3_3 2 45 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 45 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 45 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 106))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  106 (allA_of_3_1 44 44 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 43 106 (allA_succ_of_accept 42 43 106
  (Polychromatic418967fa.accept_15_12_13_1_1_3695 42 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 106 (accept_3_3 41 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 106 (Polychromatic418967fa.accept_12_4_7_10_1_563 40 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 106 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 43 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 106 (accept_3_3 38 43 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 43 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 106
  (Polychromatic418967fa.accept_11_3_10_7_1_129 36 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 106 (accept_3_3 35 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 106 (Polychromatic418967fa.accept_19_15_5_11_1_4719 34 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 43 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 106 (accept_3_3 32 43 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 106 (Polychromatic418967fa.accept_13_5_4_2_1_846 31 43 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 106
  (Polychromatic418967fa.accept_14_2_1_8_1_650 30 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 106 (accept_3_3 29 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 106 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 106 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 43 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 106 (accept_3_3 26 43 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 43 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 106
  (Polychromatic418967fa.accept_13_11_4_2_1_2954 24 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 106 (accept_3_3 23 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 106 (Polychromatic418967fa.accept_18_4_7_16_1_2307 22 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 43 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 106 (accept_3_3 20 43 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 106 (Polychromatic418967fa.accept_10_9_3_6_1_686 19 43 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 106
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 106 (accept_3_3 17 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 106 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 106 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 43 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 106 (accept_3_3 14 43 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 43 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 106
  (Polychromatic418967fa.accept_13_12_4_2_1_2955 12 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 106 (accept_3_3 11 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 106 (Polychromatic418967fa.accept_15_10_13_1_1_3698 10 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 43 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 106 (accept_3_3 8 43 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 106 (Polychromatic418967fa.accept_10_7_3_6_1_644 7 43 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 106
  (Polychromatic418967fa.accept_13_6_4_2_1_1433 6 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 106 (accept_3_3 5 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  106 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 43 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 43 106 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 43 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 106 (accept_3_3 2 43 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 43 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 106)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 42 106 (allA_succ_of_accept 41 42 106 (accept_3_3 41 42 106 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 42 106 2 20 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 42 106 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 42 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 42 106 2 19 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 106 (Polychromatic418967fa.accept_9_1_6_7_1_285 37
  42 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 106 2 18 21 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 106 (accept_3_3 35
  42 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 106 2 17 21 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42 106
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 42 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 42 106 2 16 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 42 106 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 42 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 106 2 15 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 106 (accept_3_3 29 42 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 106 2 14 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 42 106 (Polychromatic418967fa.accept_11_5_9_7_1_411 27 42 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 42 106 2 13 21 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 106
  (Polychromatic418967fa.accept_13_12_3_2_1_1470 25 42 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 106 2 12 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 42 106 (accept_3_3 23 42 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42
  106 2 11 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  42 106 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 42 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 42 106 2 10 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 42 106 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 42 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 106 2 9 21 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 106 (accept_3_3 17 42 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42 106 2 8 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 42 106 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 42 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 106 2 7 21 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 106
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 42 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 42 106 2 6 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 42 106 (accept_3_3 11 42 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42
  106 2 5 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  42 106 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 42 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 42 106 2 4 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 42 106 (Polychromatic418967fa.accept_17_7_8_4_1_1520 7 42 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 106 2 3 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 106 (accept_3_3 5 42 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 106 2 2 21 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 42 106 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 42 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 106 2 1 21 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 106
  (Polychromatic418967fa.accept_9_1_6_7_1_285 1 42 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 42 106)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 106 (allA_of_3_1 41 41 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 40 106 (allA_succ_of_accept 39 40 106
  (Polychromatic418967fa.accept_7_4_5_1_1_418 39 40 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 40 106 2 19 20 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 40 106 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 40 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 40 106 2 18 20 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 40 106 (accept_3_3 35 40 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 40 106 2 17 20 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 40 106 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 40 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 40 106 2 16 20 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 40 106
  (Polychromatic418967fa.accept_7_3_5_1_1_72 31 40 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 40 106 2 15 20 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 40 106 (accept_3_3 29 40 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 40
  106 2 14 20 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  40 106 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 40 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 40 106 2 13 20 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 40 106 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 40 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 40 106 2 12 20 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 40 106 (accept_3_3 23 40 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 40 106 2 11 20 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 40 106
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 40 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 40 106 2 10 20 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 40 106 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 40 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 40 106 2 9 20 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 40 106 (accept_3_3 17 40 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 40 106 2 8 20 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 40 106 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 40 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 40 106 2 7 20 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 40 106 (Polychromatic418967fa.accept_7_6_5_1_1_416 13
  40 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 40 106 2 6 20 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 40 106 (accept_3_3 11
  40 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40 106 2 5 20 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 40 106
  (Polychromatic418967fa.accept_13_9_1_2_1_2952 9 40 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 40 106 2 4 20 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 40 106 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 40 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 40 106 2 3 20 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 40 106 (accept_3_3 5 40 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 40 106 2 2 20 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 40 106 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 40 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 40 106 2 1 20 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 40 106 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 40
  106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  106)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 106 (allA_succ_of_accept 38 39 106 (accept_3_3 38 39 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 37
  39 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 39 106
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 36 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 39 106 (accept_3_3 35 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  39 106 (Polychromatic418967fa.accept_11_1_6_7_1_116 34 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 39 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 39 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 106 (accept_3_3 32 39 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 39 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 39 106
  (Polychromatic418967fa.accept_12_6_3_10_1_224 30 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 39 106 (accept_3_3 29 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  39 106 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 39 106 (Polychromatic418967fa.accept_19_8_1_11_1_4718 27 39 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 106 (accept_3_3 26 39 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 39 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 39 106
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 39 106 (accept_3_3 23 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  39 106 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 39 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 39 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 106 (accept_3_3 20 39 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 39 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 39 106
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 39 106 (accept_3_3 17 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  39 106 (Polychromatic418967fa.accept_17_16_5_4_1_2499 16 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 39 106 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 39 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 106 (accept_3_3 14 39 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 39 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 39 106
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 39 106 (accept_3_3 11 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  39 106 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 39 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 39 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 106 (accept_3_3 8 39 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 39 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 106
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 106 (accept_3_3 5 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39
  106 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 39 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 39 106 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 39 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 106 (accept_3_3 2 39 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 39 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 39 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 106))))))))))))))))))))))))))))))))))))))) (allB_succ 38 106
  (allA_of_3_1 38 38 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 37 106 (allA_succ_of_accept 36 37 106
  (Polychromatic418967fa.accept_11_3_4_7_1_114 36 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 106 (accept_3_3 35 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  37 106 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 37 106 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 37 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 106 (accept_3_3 32 37 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 37 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 106
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 106 (accept_3_3 29 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 106 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 37 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 106 (accept_3_3 26 37 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 106 (Polychromatic418967fa.accept_11_3_4_7_1_114 25 37 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 106
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 106 (accept_3_3 23 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 106 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 106 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 37 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 106 (accept_3_3 20 37 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 37 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 106
  (Polychromatic418967fa.accept_25_18_12_6_1_4717 18 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 106 (accept_3_3 17 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 106 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 37 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 106 (accept_3_3 14 37 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 106 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 37 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 106
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 106 (accept_3_3 11 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 106 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 106 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 37 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 106 (accept_3_3 8 37 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 37 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 106
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 106 (accept_3_3 5 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  106 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 37 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 37 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 106 (accept_3_3 2 37 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 106 (Polychromatic418967fa.accept_10_1_7_6_1_91 1 37 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 106))))))))))))))))))))))))))))))))))))) (allB_succ 36 106
  (allA_succ_of_accept 35 36 106 (accept_3_3 35 36 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36
  106 2 17 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  36 106 (Polychromatic418967fa.accept_15_3_6_1_1_1834 33 36 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 36 106 2 16 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 36 106 (Polychromatic418967fa.accept_13_5_10_2_1_856 31 36 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 106 2 15 18 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 106 (accept_3_3 29 36 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 106 2 14 18 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 106
  (Polychromatic418967fa.accept_19_8_17_11_1_3406 27 36 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 36 106 2 13 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 36 106 (Polychromatic418967fa.accept_13_12_10_2_1_1451 25 36 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 106 2 12 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 106 (accept_3_3 23 36 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 106 2 11 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 36 106 (Polychromatic418967fa.accept_11_10_3_7_1_2564 21 36 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 36 106 2 10 18 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 106
  (Polychromatic418967fa.accept_13_6_10_2_1_1449 19 36 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 106 2 9 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 106 (accept_3_3 17 36 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36
  106 2 8 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  36 106 (Polychromatic418967fa.accept_11_4_3_7_1_828 15 36 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 36 106 2 7 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 36 106 (Polychromatic418967fa.accept_19_13_17_11_1_4716 13 36 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 106 2 6 18 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 106 (accept_3_3 11 36 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36 106 2 5 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 36 106 (Polychromatic418967fa.accept_15_9_6_1_1_493 9 36 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 36 106 2 4 18 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 106
  (Polychromatic418967fa.accept_15_7_6_1_1_1091 7 36 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 36 106 2 3 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 36 106 (accept_3_3 5 36 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 106
  2 2 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 36
  106 (Polychromatic418967fa.accept_13_3_10_2_1_381 3 36 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 36 106 2 1 18 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 36 106 (Polychromatic418967fa.accept_20_1_16_6_1_4715 1 36 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 106)))))))))))))))))))))))))))))))))))) (allB_succ 35 106
  (allA_of_3_1 35 35 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 34 106 (allA_succ_of_accept 33 34 106
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 34 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 34 106 2 16 17 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 34 106 (Polychromatic418967fa.accept_20_11_14_6_1_4714 31 34 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 34 106 2 15 17 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 34 106 (accept_3_3 29 34 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 34 106 2 14 17 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 34 106 (Polychromatic418967fa.accept_15_12_4_1_1_3746 27 34 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 34 106 2 13 17 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 34 106
  (Polychromatic418967fa.accept_10_5_4_6_1_319 25 34 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 34 106 2 12 17 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 34 106 (accept_3_3 23 34 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34
  106 2 11 17 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  34 106 (Polychromatic418967fa.accept_14_7_6_8_1_2856 21 34 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 34 106 2 10 17 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 34 106 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 34 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 34 106 2 9 17 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 34 106 (accept_3_3 17 34 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 34 106 2 8 17 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 34 106 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 34 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 34 106 2 7 17 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 34 106
  (Polychromatic418967fa.accept_26_13_8_2_1_4713 13 34 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 34 106 2 6 17 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 34 106 (accept_3_3 11 34 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34
  106 2 5 17 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  34 106 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 34 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 34 106 2 4 17 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 34 106 (Polychromatic418967fa.accept_13_7_8_2_1_1483 7 34 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 106 2 3 17 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 106 (accept_3_3 5 34 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 34 106 2 2 17 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 34 106 (Polychromatic418967fa.accept_15_3_4_1_1_1072 3 34 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 106 2 1 17 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 106
  (Polychromatic418967fa.accept_19_1_15_11_1_4712 1 34 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 34 106)))))))))))))))))))))))))))))))))) (allB_succ 33 106 (allA_succ_of_accept 32 33 106 (accept_3_3 32 33
  106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 106 (Polychromatic418967fa.accept_4_3_1_2_1_62
  31 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 106
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 33 106 (accept_3_3 29 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  33 106 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 33 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 33 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 106 (accept_3_3 26 33 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 33 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 106
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 33 106 (accept_3_3 23 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  33 106 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 33 106 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 33 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 106 (accept_3_3 20 33 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 33 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 106
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 33 106 (accept_3_3 17 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  33 106 (Polychromatic418967fa.accept_19_16_14_11_1_4711 16 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 33 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 33 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 106 (accept_3_3 14 33 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 33 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 106
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 33 106 (accept_3_3 11 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  33 106 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 33 106 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 33 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 106 (accept_3_3 8 33 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 33 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 106
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 106 (accept_3_3 5 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33
  106 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 33 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 33 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 33 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 106 (accept_3_3 2 33 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 33 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 33 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 106))))))))))))))))))))))))))))))))) (allB_succ 32 106
  (allA_of_3_1 32 32 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 106 (allA_succ_of_accept 30 31 106
  (Polychromatic418967fa.accept_7_2_3_1_1_10 30 31 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 106 (accept_3_3 29 31 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  31 106 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 31 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 106 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 31 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 106 (accept_3_3 26 31 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 31 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 106
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 31 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 106 (accept_3_3 23 31 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 106 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 31 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 31 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 106 (accept_3_3 20 31 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 106 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 31 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 106
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 31 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 106 (accept_3_3 17 31 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 106 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 31 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 106 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 31 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 106 (accept_3_3 14 31 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 31 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 106
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 31 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 106 (accept_3_3 11 31 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 106 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 31 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 31 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 106 (accept_3_3 8 31 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 106 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 31 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 106
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 31 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 106 (accept_3_3 5 31 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  106 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 31 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 106 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 31 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 106 (accept_3_3 2 31 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 31 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 106))))))))))))))))))))))))))))))) (allB_succ 30 106
  (allA_succ_of_accept 29 30 106 (accept_3_3 29 30 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30
  106 2 14 15 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  30 106 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 30 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 30 106 2 13 15 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 30 106 (Polychromatic418967fa.accept_13_12_4_2_1_2955 25 30 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 106 2 12 15 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 106 (accept_3_3 23 30 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 106 2 11 15 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 30 106
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 30 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 106 2 10 15 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 106 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 30 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 106 2 9 15 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 106 (accept_3_3 17 30 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 30 106 2 8 15 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 30 106 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 30 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 30 106 2 7 15 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 106 (Polychromatic418967fa.accept_7_6_2_1_1_214 13
  30 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 106 2 6 15 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 106 (accept_3_3 11
  30 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 106 2 5 15 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 30 106
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 30 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 30 106 2 4 15 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 30 106 (Polychromatic418967fa.accept_16_7_14_10_1_3544 7 30 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 106 2 3 15 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 106 (accept_3_3 5 30 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 30 106 2 2 15 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 30 106 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 30 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 106 2 1 15 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 106 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 30
  106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 106))))))))))))))))))))))))))))))
  (allB_succ 29 106 (allA_of_3_1 29 29 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 106
  (allA_succ_of_accept 27 28 106 (Polychromatic418967fa.accept_15_12_13_1_1_3695 27 28 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 28 106 2 13 14 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 28 106 (Polychromatic418967fa.accept_12_1_4_10_1_209
  25 28 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 106 2 12 14 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 106 (accept_3_3 23
  28 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 28 106 2 11 14 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 28 106
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 28 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 28 106 2 10 14 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 28 106 (Polychromatic418967fa.accept_12_7_4_10_1_572 19 28 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 28 106 2 9 14 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 28 106 (accept_3_3 17 28 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 28 106 2 8 14 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 28 106 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 28 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 28 106 2 7 14 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 28 106 (Polychromatic418967fa.accept_9_4_1_7_1_293 13
  28 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 28 106 2 6 14 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 28 106 (accept_3_3 11
  28 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 28 106 2 5 14 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 28 106
  (Polychromatic418967fa.accept_23_9_5_14_1_4710 9 28 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 28 106 2 4 14 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 28 106 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 28 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 28 106 2 3 14 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 28 106 (accept_3_3 5 28 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 28 106 2 2 14 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 28 106 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 28 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 28 106 2 1 14 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 28 106 (Polychromatic418967fa.accept_11_1_6_7_1_116 1
  28 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 106))))))))))))))))))))))))))))
  (allB_succ 27 106 (allA_succ_of_accept 26 27 106 (accept_3_3 26 27 106 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 27 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 106 (Polychromatic418967fa.accept_21_3_6_1_1_4709 24 27 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 106 (accept_3_3 23 27 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 106 (Polychromatic418967fa.accept_13_9_1_2_1_2952
  22 27 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 106
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 27 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 27 106 (accept_3_3 20 27 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  27 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 27 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 27 106 (Polychromatic418967fa.accept_12_6_3_10_1_224 18 27 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 106 (accept_3_3 17 27 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 106 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 27 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 106
  (Polychromatic418967fa.accept_16_15_11_10_1_3639 15 27 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 27 106 (accept_3_3 14 27 106 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 27 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 106 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 27 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 106 (accept_3_3 11 27 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 106
  (Polychromatic418967fa.accept_19_10_8_11_1_4708 10 27 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 27 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 27 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 106 (accept_3_3 8 27 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 27 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 27 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27 106 (Polychromatic418967fa.accept_12_6_3_10_1_224 6
  27 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 106 (accept_3_3 5 27 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 106 (Polychromatic418967fa.accept_15_4_12_1_1_1081
  4 27 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 106
  (Polychromatic418967fa.accept_10_3_7_6_1_659 3 27 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 27 106 (accept_3_3 2 27 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27
  106 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 27 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 27 106))))))))))))))))))))))))))) (allB_succ 26 106 (allA_of_3_1 26 26 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 25 106 (allA_succ_of_accept 24 25 106 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 25 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 106 (accept_3_3 23 25 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 25 106 (Polychromatic418967fa.accept_15_7_10_1_1_1836
  22 25 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 106
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 25 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 25 106 (accept_3_3 20 25 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  25 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 25 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 25 106 (Polychromatic418967fa.accept_13_5_12_2_1_1423 18 25 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 106 (accept_3_3 17 25 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 25 106 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 25 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 25 106
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 25 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 25 106 (accept_3_3 14 25 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  25 106 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 25 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 25 106 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 25 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 106 (accept_3_3 11 25 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 25 106 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 25 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 25 106
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 25 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 25 106 (accept_3_3 8 25 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25
  106 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 25 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 25 106 (Polychromatic418967fa.accept_13_6_12_2_1_4707 6 25 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 25 106 (accept_3_3 5 25 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 25 106 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 25 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 25
  106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 106 (accept_3_3 2 25 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 106 (Polychromatic418967fa.accept_10_1_5_6_1_649 1
  25 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 106)))))))))))))))))))))))))
  (allB_succ 24 106 (allA_succ_of_accept 23 24 106 (accept_3_3 23 24 106 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 24 106 2 11 12 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 24 106 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 24 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 24 106 2 10 12 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 24 106 (Polychromatic418967fa.accept_7_5_3_1_1_424 19
  24 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 106 2 9 12 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 106 (accept_3_3 17
  24 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 24 106 2 8 12 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 24 106
  (Polychromatic418967fa.accept_10_5_4_6_1_319 15 24 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 24 106 2 7 12 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 24 106 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 24 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 106 2 6 12 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 106 (accept_3_3 11 24 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 24 106 2 5 12 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 24 106 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 24 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 24 106 2 4 12 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 24 106 (Polychromatic418967fa.accept_15_7_9_1_1_473 7
  24 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 106 2 3 12 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 106 (accept_3_3 5 24
  106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 106 2 2 12 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 24 106
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 24 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 24 106 2 1 12 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 24 106 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 24 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 24 106)))))))))))))))))))))))) (allB_succ 23 106 (allA_of_3_1 23 23 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 22 106 (allA_succ_of_accept 21 22 106
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 22 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 22 106 2 10 11 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 22 106 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 22 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 22 106 2 9 11 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 22 106 (accept_3_3 17 22 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 22 106 2 8 11 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 22 106 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 22 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 22 106 2 7 11 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 22 106 (Polychromatic418967fa.accept_19_13_3_11_1_4706
  13 22 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 22 106 2 6 11 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 22 106 (accept_3_3 11
  22 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 22 106 2 5 11 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 22 106
  (Polychromatic418967fa.accept_15_9_7_1_1_1075 9 22 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 22 106 2 4 11 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 22 106 (Polychromatic418967fa.accept_13_7_9_2_1_2167 7 22 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 22 106 2 3 11 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 22 106 (accept_3_3 5 22 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 22 106 2 2 11 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 22 106 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 22 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 22 106 2 1 11 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 22 106 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 22
  106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 106)))))))))))))))))))))) (allB_succ 21
  106 (allA_succ_of_accept 20 21 106 (accept_3_3 20 21 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 21 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 21 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 21 106 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 21 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 106 (accept_3_3 17 21 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 106 (Polychromatic418967fa.accept_19_16_2_11_1_4705 16 21 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 106
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 21 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 21 106 (accept_3_3 14 21 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  21 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 21 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 21 106 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 21 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 106 (accept_3_3 11 21 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 106 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 21 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 106
  (Polychromatic418967fa.accept_15_9_6_1_1_493 9 21 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 21 106 (accept_3_3 8 21 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21
  106 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 21 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 21 106 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 21 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 106 (accept_3_3 5 21 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 21 106 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 21 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 21
  106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 106 (accept_3_3 2 21 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 21
  106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 106))))))))))))))))))))) (allB_succ 20
  106 (allA_of_3_1 20 20 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 106 (allA_succ_of_accept 18 19 106
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 19 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 106 (accept_3_3 17 19 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 106 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 19 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 106 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 19 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 106 (accept_3_3 14 19 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 19 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 106
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 19 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 106 (accept_3_3 11 19 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 106 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 19 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 19 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 106 (accept_3_3 8 19 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 106 (Polychromatic418967fa.accept_16_7_3_10_1_3614 7 19 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 106
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 19 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 106 (accept_3_3 5 19 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  106 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 19 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 106 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 19 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 106 (accept_3_3 2 19 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 19 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 106))))))))))))))))))) (allB_succ 18 106 (allA_succ_of_accept 17
  18 106 (accept_3_3 17 18 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 106 2 8 9 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 106
  (Polychromatic418967fa.accept_12_3_6_10_1_576 15 18 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 18 106 2 7 9 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 106 (Polychromatic418967fa.accept_10_3_8_6_1_326 13 18 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 106 2 6 9 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 106 (accept_3_3 11 18 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 106 2 5 9 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 18 106 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 18 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 106 2 4 9 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 106 (Polychromatic418967fa.accept_13_7_5_2_1_401 7
  18 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 106 2 3 9 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 106 (accept_3_3 5 18
  106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 106 2 2 9 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 106
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 18 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 106 2 1 9 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 106 (Polychromatic418967fa.accept_19_1_18_11_1_4704 1 18 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 18 106)))))))))))))))))) (allB_succ 17 106 (allA_of_3_1 17 17 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 16 106 (allA_succ_of_accept 15 16 106
  (Polychromatic418967fa.accept_14_1_2_8_1_655 15 16 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 16 106 2 7 8 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 16 106 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 16 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 16 106 2 6 8 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 16 106 (accept_3_3 11 16 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 16 106 2 5 8 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 16 106 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 16 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 16 106 2 4 8 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 16 106 (Polychromatic418967fa.accept_12_7_4_10_1_572 7
  16 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 106 2 3 8 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 106 (accept_3_3 5 16
  106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 106 2 2 8 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 16 106
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 16 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 16 106 2 1 8 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 16 106 (Polychromatic418967fa.accept_12_1_4_10_1_209 1 16 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 16 106)))))))))))))))) (allB_succ 15 106 (allA_succ_of_accept 14 15 106
  (accept_3_3 14 15 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 106
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 15 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 15 106 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 15 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 106 (accept_3_3 11 15 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 15 106 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 15 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 15
  106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 106 (accept_3_3 8 15 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 15
  106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 106
  (Polychromatic418967fa.accept_12_6_3_10_1_224 6 15 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 106 (accept_3_3 5 15 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15
  106 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 15 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 15 106 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 15 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 106 (accept_3_3 2 15 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 15 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 15 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 106))))))))))))))) (allB_succ 14 106 (allA_of_3_1 14 14 106
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 106 (allA_succ_of_accept 12 13 106
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 13 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 106 (accept_3_3 11 13 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 106 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 13 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 106 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 13 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 106 (accept_3_3 8 13 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 13 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 106
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 13 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 106 (accept_3_3 5 13 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  106 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 13 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 13 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 13 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 106 (accept_3_3 2 13 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 106 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 13 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 106))))))))))))) (allB_succ 12 106
  (allA_succ_of_accept 11 12 106 (accept_3_3 11 12 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12
  106 2 5 6 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 12
  106 (Polychromatic418967fa.accept_17_9_12_4_1_3468 9 12 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 12 106 2 4 6 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 12 106 (Polychromatic418967fa.accept_17_7_12_4_1_2524 7 12 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 106 2 3 6 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 106 (accept_3_3 5 12 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 106 2 2 6 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 12 106 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 12 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 106 2 1 6 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 106
  (Polychromatic418967fa.accept_9_1_3_7_1_6 1 12 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 12 106)))))))))))) (allB_succ 11 106 (allA_of_3_1 11 11 106 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 10 106 (allA_succ_of_accept 9 10 106 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 10 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 10 106 2 4 5 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 10 106
  (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 10 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 10 106 2 3 5 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 10 106 (accept_3_3 5 10 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 10 106
  2 2 5 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 10 106
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 10 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 10 106 2 1 5 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 10 106 (Polychromatic418967fa.accept_18_1_10_16_1_566 1 10 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 10 106)))))))))) (allB_succ 9 106 (allA_succ_of_accept 8 9 106 (accept_3_3 8
  9 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 106 (Polychromatic418967fa.accept_4_3_1_2_1_62
  7 9 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 106
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 9 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 106 (accept_3_3 5 9 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 106
  (Polychromatic418967fa.accept_25_4_9_6_1_4703 4 9 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 9 106 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 9 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 106 (accept_3_3 2 9 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 9 106 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 9 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 106))))))))) (allB_succ 8 106 (allA_of_3_1 8 8 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 7 106 (allA_succ_of_accept 6 7 106
  (Polychromatic418967fa.accept_14_6_7_8_1_624 6 7 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 106 (accept_3_3 5 7 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 106
  (Polychromatic418967fa.accept_12_4_7_10_1_563 4 7 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 106 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 7 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 106 (accept_3_3 2 7 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 7 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 106))))))) (allB_succ 6 106 (allA_succ_of_accept 5 6 106
  (accept_3_3 5 6 106 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 106 2 2 3 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 106
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 6 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 106 2 1 3 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 106 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 6 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 6 106)))))) (allB_succ 5 106 (allA_of_3_1 5 5 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 4 106 (allA_succ_of_accept 3 4 106 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 4 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 4 106 2 1 2 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 4 106
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 4 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 106)))) (allB_succ 3 106 (allA_succ_of_accept 2 3 106 (accept_3_3 2 3 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 106 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 3 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 106))) (allB_succ 2 106 (allA_of_3_1 2 2 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  106))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


