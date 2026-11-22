-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch126
-- name    : Polychromatic418967fa_Branch126
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:13:37.515264+00:00
-- url     : https://prove2.me/theorems/ca2b565f-d169-446d-930c-99c8c2e736b7
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

def Polychromatic418967fa.branch_126 : allB 126 126 :=
  allB_succ' 2 125 126 (Eq.refl Bool.true) (allA_succ_of_accept 1 125 126 (accept_3_4 1 125 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 125 126)) (allB_succ' 3 124 126 (Eq.refl Bool.true) (allA_succ_of_gcd 2 124 126 2 1 62
  63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 124 126
  (Polychromatic418967fa.accept_27_1_16_18_1_2547 1 124 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 124 126))) (allB_succ' 4 123 126 (Eq.refl Bool.true) (allA_succ_of_gcd 3 123 126 3 1 41 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 123 126
  (Polychromatic418967fa.accept_12_2_3_6_1_112 2 123 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 123 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 123 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 123 126)))) (allB_succ' 5 122 126 (Eq.refl Bool.true) (allA_succ_of_gcd 4
  122 126 2 2 61 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  3 122 126 (Polychromatic418967fa.accept_12_3_2_6_1_138 3 122 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 122 126 2 1 61 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 122 126 (accept_3_4 1 122 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  126))))) (allB_succ' 6 121 126 (Eq.refl Bool.true) (allA_succ_of_accept 5 121 126 (accept_3_5 5 121 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 126 (Polychromatic418967fa.accept_16_4_9_14_1_3883 4 121
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 126
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 121 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 126 (accept_3_5 2 121 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 126 (Polychromatic418967fa.accept_19_1_7_12_1_3443 1 121 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121 126)))))) (allB_succ' 7 120 126 (Eq.refl Bool.true) (allA_succ_of_gcd 6 120 126 6 1 20 21
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 120 126
  (Polychromatic418967fa.accept_13_5_3_9_1_1189 5 120 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 120 126 2 2 60 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 120 126 3 1 40 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 120 126 2 1 60 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 120 126 (Polychromatic418967fa.accept_31_1_27_2_1_6276 1 120 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 120 126))))))) (allB_succ' 8 119 126 (Eq.refl Bool.true) (allA_succ_of_gcd 7
  119 126 7 1 17 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  6 119 126 (Polychromatic418967fa.accept_13_6_2_9_1_1188 6 119 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 119 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 119 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 126 (accept_3_4 4 119 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 126 (Polychromatic418967fa.accept_10_3_9_6_1_94 3 119 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 126
  (Polychromatic418967fa.accept_22_2_9_16_1_6269 2 119 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 126 (accept_3_4 1 119 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  126)))))))) (allB_succ' 9 118 126 (Eq.refl Bool.true) (allA_succ_of_gcd 8 118 126 2 4 59 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 118 126
  (Polychromatic418967fa.accept_15_7_13_6_1_696 7 118 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 118 126 2 3 59 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 118 126 (accept_3_5 5 118 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 118
  126 2 2 59 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  118 126 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 118 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 118 126 2 1 59 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 118 126 (Polychromatic418967fa.accept_19_1_4_12_1_6275 1 118 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118 126))))))))) (allB_succ' 10 117 126 (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 117 126 9 1 13 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 117 126 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 117 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 117 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 117 126 3 2 39 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 117 126
  (Polychromatic418967fa.accept_15_5_12_6_1_639 5 117 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 117 126 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 117 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 117 126 3 1 39 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 117 126 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 117 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 126
  (Polychromatic418967fa.accept_10_1_7_6_1_91 1 117 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 117 126)))))))))) (allB_succ' 11 116 126 (Eq.refl Bool.true) (allA_succ_of_gcd 10 116 126 2 5 58 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 116 126
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 116 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 116 126 2 4 58 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 116 126 (accept_3_4 7 116 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 116
  126 2 3 58 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  116 126 (Polychromatic418967fa.accept_15_5_11_6_1_692 5 116 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 116 126 2 2 58 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 116 126 (Polychromatic418967fa.accept_12_3_8_6_1_895 3 116 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 116 126 2 1 58 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 116 126 (accept_3_4 1 116 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 116 126))))))))))) (allB_succ' 12 115 126 (Eq.refl Bool.true) (allA_succ_of_accept 11
  115 126 (accept_3_5 11 115 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 115 126
  (Polychromatic418967fa.accept_20_10_15_6_1_2149 10 115 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 115 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 115 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 115 126 (accept_3_5 8 115 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 115 126 (Polychromatic418967fa.accept_13_7_11_9_1_1858 7 115 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 126
  (Polychromatic418967fa.accept_17_6_13_7_1_272 6 115 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 115 126 (accept_3_5 5 115 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  115 126 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 115 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 115 126 (Polychromatic418967fa.accept_15_3_10_6_1_632 3 115 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 126 (accept_3_5 2 115 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 115 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115 126)))))))))))) (allB_succ' 13 114 126 (Eq.refl
  Bool.true) (allA_succ_of_gcd 12 114 126 6 2 19 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 114 126 (Polychromatic418967fa.accept_15_11_9_6_1_1321 11 114 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 114 126 2 5 57 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 114 126 3 3 38 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 114 126 2 4 57 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 114 126
  (Polychromatic418967fa.accept_23_7_22_11_1_6274 7 114 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 114 126 6 1 19 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 114 126 (Polychromatic418967fa.accept_10_5_4_6_1_319 5 114 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 114 126 2 2 57 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 114 126 3 1 38 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 114 126 2 1 57 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 126 (Polychromatic418967fa.accept_13_1_10_9_1_215 1 114 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114 126))))))))))))) (allB_succ' 14 113 126
  (Eq.refl Bool.true) (allA_succ_of_accept 13 113 126 (accept_3_4 13 113 126 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 113 126 (Polychromatic418967fa.accept_24_12_17_6_1_6206 12 113 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 113 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 11
  113 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 126 (accept_3_4 10
  113 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 126
  (Polychromatic418967fa.accept_10_9_3_6_1_686 9 113 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 113 126 (Polychromatic418967fa.accept_10_8_3_6_1_685 8 113 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 113 126 (accept_3_4 7 113 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 113 126 (Polychromatic418967fa.accept_19_6_18_12_1_6125 6 113 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 113 126
  (Polychromatic418967fa.accept_17_5_11_7_1_6146 5 113 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 113 126 (accept_3_4 4 113 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  113 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 113 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 113 126 (Polychromatic418967fa.accept_15_2_8_6_1_1340 2 113 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 113 126 (accept_3_4 1 113 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 113 126)))))))))))))) (allB_succ' 15 112 126 (Eq.refl Bool.true) (allA_succ_of_gcd 14
  112 126 14 1 8 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  13 112 126 (Polychromatic418967fa.accept_15_13_7_6_1_682 13 112 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 112 126 2 6 56 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 112 126 (accept_3_5 11 112 126 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 112 126 2 5 56 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 112 126 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 112 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 112 126 2 4 56 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 112 126 7 1 16 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 112 126 2 3 56 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 112 126 (accept_3_5 5 112 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 112 126 2 2 56 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 112 126 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 112 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 112 126 2 1 56 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 112 126 (Polychromatic418967fa.accept_10_1_2_6_1_638 1
  112 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112 126))))))))))))))) (allB_succ' 16
  111 126 (Eq.refl Bool.true) (allA_succ_of_gcd 15 111 126 3 5 37 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 111 126 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 111 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 126
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 111 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 111 126 3 4 37 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 111 126 (Polychromatic418967fa.accept_13_11_7_9_1_612 11 111 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 126 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 111
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 111 126 3 3 37 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 111 126
  (Polychromatic418967fa.accept_12_8_3_6_1_909 8 111 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 111 126 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 111 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 111 126 3 2 37 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 111 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 111 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 126
  (Polychromatic418967fa.accept_12_4_3_6_1_879 4 111 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 111 126 3 1 37 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 111 126 (Polychromatic418967fa.accept_10_2_1_6_1_634 2 111 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 111 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111 126)))))))))))))))) (allB_succ' 17 110 126
  (Eq.refl Bool.true) (allA_succ_of_gcd 16 110 126 2 8 55 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 110 126 (Polychromatic418967fa.accept_12_3_2_6_1_138 15 110 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 110 126 2 7 55 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 110 126 (accept_3_4 13 110 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 110 126 2 6 55 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 110 126
  (Polychromatic418967fa.accept_15_11_5_6_1_669 11 110 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 110 126 2 5 55 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 110 126 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 110 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 110 126 2 4 55 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 110 126 (accept_3_4 7 110 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 110 126 2 3 55 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 110 126 (Polychromatic418967fa.accept_19_5_15_12_1_6273 5 110 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 110 126 2 2 55 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 110 126
  (Polychromatic418967fa.accept_12_3_2_6_1_138 3 110 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 110 126 2 1 55 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 110 126 (accept_3_4 1 110 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  126))))))))))))))))) (allB_succ' 18 109 126 (Eq.refl Bool.true) (allA_succ_of_accept 17 109 126 (accept_3_5 17 109 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 109 126 (Polychromatic418967fa.accept_13_3_5_9_1_5285
  16 109 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 109 126
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 109 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 109 126 (accept_3_5 14 109 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 109 126 (Polychromatic418967fa.accept_10_3_9_6_1_94 13 109 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 109 126 (Polychromatic418967fa.accept_24_12_13_6_1_6095 12 109 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 126 (accept_3_5 11 109 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 126 (Polychromatic418967fa.accept_15_10_4_6_1_2129 10 109
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 126
  (Polychromatic418967fa.accept_15_9_4_6_1_3075 9 109 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 126 (accept_3_5 8 109 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 109 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 126 (Polychromatic418967fa.accept_11_6_10_5_1_341 6 109 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 126 (accept_3_5 5 109 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 126 (Polychromatic418967fa.accept_11_4_10_5_1_1202 4 109 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 126
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 109 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 126 (accept_3_5 2 109 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 126 (Polychromatic418967fa.accept_13_1_5_9_1_226 1 109 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109 126)))))))))))))))))) (allB_succ' 19 108 126 (Eq.refl Bool.true) (allA_succ_of_gcd 18 108
  126 18 1 6 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  108 126 (Polychromatic418967fa.accept_24_17_12_6_1_6190 17 108 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 108 126 2 8 54 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 15 108 126 3 5 36 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 14 108 126 2 7 54 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 108 126 (Polychromatic418967fa.accept_10_3_8_6_1_326 13 108 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 126 6 2 18 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 126
  (Polychromatic418967fa.accept_15_11_3_6_1_1306 11 108 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 108 126 2 5 54 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 108 126 9 1 12 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 108 126 2 4 54 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 108 126 (Polychromatic418967fa.accept_11_7_9_5_1_338 7 108 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 126 6 1 18 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 126 (Polychromatic418967fa.accept_13_5_4_9_1_601 5 108 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 108 126 2 2 54 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 108 126 3 1 36 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 108 126 2 1 54 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 108 126
  (Polychromatic418967fa.accept_15_1_3_6_1_621 1 108 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 108 126))))))))))))))))))) (allB_succ' 20 107 126 (Eq.refl Bool.true) (allA_succ_of_accept 19 107 126
  (accept_3_4 19 107 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 107 126
  (Polychromatic418967fa.accept_13_5_3_9_1_1189 18 107 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 107 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 107 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 126 (accept_3_4 16 107 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 107 126 (Polychromatic418967fa.accept_13_2_3_9_1_2610 15 107 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 126
  (Polychromatic418967fa.accept_11_3_8_5_1_336 14 107 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 107 126 (accept_3_4 13 107 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 107 126 (Polychromatic418967fa.accept_13_12_3_9_1_4341 12 107 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 107 126 (Polychromatic418967fa.accept_10_1_7_6_1_91 11 107 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 126 (accept_3_4 10 107 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 107 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 126
  (Polychromatic418967fa.accept_13_8_3_9_1_5269 8 107 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 107 126 (accept_3_4 7 107 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 126 (Polychromatic418967fa.accept_13_6_3_9_1_1827 6 107 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 107 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 126 (accept_3_4 4 107 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 126 (Polychromatic418967fa.accept_10_3_7_6_1_659 3 107 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 126
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 2 107 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 126 (accept_3_4 1 107 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  126)))))))))))))))))))) (allB_succ' 21 106 126 (Eq.refl Bool.true) (allA_succ_of_gcd 20 106 126 2 10 53 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 106 126
  (Polychromatic418967fa.accept_13_6_2_9_1_1188 19 106 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 106 126 2 9 53 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 106 126 (accept_3_5 17 106 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  106 126 2 8 53 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 106 126 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 106 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 106 126 2 7 53 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 106 126 (Polychromatic418967fa.accept_16_13_10_14_1_2871 13 106 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 106 126 2 6 53 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 106 126 (accept_3_5 11
  106 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 106 126 2 5 53 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 106 126
  (Polychromatic418967fa.accept_11_9_7_5_1_749 9 106 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 106 126 2 4 53 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 106 126 (Polychromatic418967fa.accept_13_7_2_9_1_1826 7 106 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 106 126 2 3 53 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 106 126 (accept_3_5 5 106 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 106 126 2 2 53 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 106 126 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 106 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 106 126 2 1 53 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 106 126 (Polychromatic418967fa.accept_13_1_2_9_1_1186 1
  106 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106 126)))))))))))))))))))))
  (allB_succ' 22 105 126 (Eq.refl Bool.true) (allA_succ_of_gcd 21 105 126 21 1 5 6 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 105 126
  (Polychromatic418967fa.accept_12_8_9_6_1_127 20 105 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 105 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 105 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 105 126 3 6 35 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 105 126
  (Polychromatic418967fa.accept_19_17_10_12_1_6157 17 105 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 105 126 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 105 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 105 126 3 5 35 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 105 126 7 2 15 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 105 126
  (Polychromatic418967fa.accept_25_13_5_1_1_2727 13 105 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 105 126 3 4 35 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 105 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 105 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 126 (Polychromatic418967fa.accept_11_10_6_5_1_1239 10 105
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 105 126 3 3 35 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 105 126
  (Polychromatic418967fa.accept_12_8_9_6_1_127 8 105 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 105 126 7 1 15 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 105 126 3 2 35 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 105 126 (Polychromatic418967fa.accept_13_5_1_9_1_618 5 105 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 126 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 105 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 105 126 3 1 35 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 105 126
  (Polychromatic418967fa.accept_12_2_9_6_1_439 2 105 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 126 (Polychromatic418967fa.accept_10_1_5_6_1_649 1 105 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 105 126)))))))))))))))))))))) (allB_succ' 23 104 126 (Eq.refl Bool.true)
  (allA_succ_of_gcd 22 104 126 2 11 52 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 104 126 (Polychromatic418967fa.accept_12_9_8_6_1_466 21 104 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 104 126 2 10 52 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 104 126 (accept_3_4 19 104 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 104 126 2 9 52 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 104 126 (Polychromatic418967fa.accept_24_17_8_6_1_6246
  17 104 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 104 126 2 8 52 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 104 126
  (Polychromatic418967fa.accept_10_5_4_6_1_319 15 104 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 104 126 2 7 52 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 104 126 (accept_3_4 13 104 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  104 126 2 6 52 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 104 126 (Polychromatic418967fa.accept_33_11_5_27_1_6272 11 104 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 104 126 2 5 52 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 104 126 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 104 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 104 126 2 4 52 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 104 126 (accept_3_4 7 104 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 104 126 2 3 52 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 104 126 (Polychromatic418967fa.accept_10_5_4_6_1_319 5 104 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 104 126 2 2 52 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 104 126
  (Polychromatic418967fa.accept_12_3_8_6_1_895 3 104 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 104 126 2 1 52 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 104 126 (accept_3_4 1 104 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  126))))))))))))))))))))))) (allB_succ' 24 103 126 (Eq.refl Bool.true) (allA_succ_of_accept 23 103 126 (accept_3_5 23
  103 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 126
  (Polychromatic418967fa.accept_15_7_13_6_1_696 22 103 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 103 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 103 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 103 126 (accept_3_5 20 103 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 103 126 (Polychromatic418967fa.accept_10_9_3_6_1_686 19 103 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 103 126
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 103 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 103 126 (accept_3_5 17 103 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 103 126 (Polychromatic418967fa.accept_13_3_12_9_1_1193 16 103 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 103 126 (Polychromatic418967fa.accept_16_15_7_14_1_2883 15 103 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 103 126 (accept_3_5 14 103 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 103 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 103 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 103 126
  (Polychromatic418967fa.accept_24_12_7_6_1_6244 12 103 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 103 126 (accept_3_5 11 103 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 103 126 (Polychromatic418967fa.accept_11_10_4_5_1_359 10 103 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 103 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 103 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 103 126 (accept_3_5 8 103 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 103 126 (Polychromatic418967fa.accept_10_7_3_6_1_644 7 103 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 103 126
  (Polychromatic418967fa.accept_19_6_8_12_1_6271 6 103 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 103 126 (accept_3_5 5 103 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  103 126 (Polychromatic418967fa.accept_15_4_13_6_1_642 4 103 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 103 126 (Polychromatic418967fa.accept_13_3_12_9_1_1193 3 103 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 103 126 (accept_3_5 2 103 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 103 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 103 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 103 126)))))))))))))))))))))))) (allB_succ' 25
  102 126 (Eq.refl Bool.true) (allA_succ_of_gcd 24 102 126 6 4 17 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 102 126 (Polychromatic418967fa.accept_19_4_7_12_1_6201 23 102
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 102 126 2 11 51 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 102 126 3 7 34 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 102 126 2 10 51 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 102 126
  (Polychromatic418967fa.accept_11_8_3_5_1_355 19 102 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 126 6 3 17 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 126 (Polychromatic418967fa.accept_15_2_12_6_1_3063 17 102 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 102 126 2 8 51 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 102 126 3 5 34 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 102 126 2 7 51 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 102 126
  (Polychromatic418967fa.accept_22_13_14_16_1_6124 13 102 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 102 126 6 2 17 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 102 126 (Polychromatic418967fa.accept_10_1_2_6_1_638 11 102 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 102 126 2 5 51 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 102 126 3 3 34 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 102 126 2 4 51 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 102 126
  (Polychromatic418967fa.accept_13_7_11_9_1_1858 7 102 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 102 126 6 1 17 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 102 126 (Polychromatic418967fa.accept_15_5_12_6_1_639 5 102 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 102 126 2 2 51 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 102 126 3 1 34 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 102 126 2 1 51 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 126 (Polychromatic418967fa.accept_10_1_2_6_1_638 1 102 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102 126))))))))))))))))))))))))) (allB_succ' 26
  101 126 (Eq.refl Bool.true) (allA_succ_of_accept 25 101 126 (accept_3_4 25 101 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 101 126 (Polychromatic418967fa.accept_15_9_11_6_1_637 24 101 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 101 126
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 101 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 101 126 (accept_3_4 22 101 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 101 126 (Polychromatic418967fa.accept_19_2_6_12_1_6270 21 101 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 101 126 (Polychromatic418967fa.accept_15_5_11_6_1_692 20 101 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 101 126 (accept_3_4 19 101 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 101 126 (Polychromatic418967fa.accept_15_3_11_6_1_3083 18 101
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 101 126
  (Polychromatic418967fa.accept_10_7_1_6_1_673 17 101 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 101 126 (accept_3_4 16 101 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 101 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 101 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 101 126 (Polychromatic418967fa.accept_13_1_10_9_1_215 14 101 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 101 126 (accept_3_4 13 101 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 101 126 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 101
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 101 126
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 101 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 101 126 (accept_3_4 10 101 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  101 126 (Polychromatic418967fa.accept_15_9_11_6_1_637 9 101 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 101 126 (Polychromatic418967fa.accept_11_8_2_5_1_1769 8 101 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 101 126 (accept_3_4 7 101 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 101 126 (Polychromatic418967fa.accept_13_6_10_9_1_4329 6 101 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 101 126
  (Polychromatic418967fa.accept_10_5_1_6_1_672 5 101 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 101 126 (accept_3_4 4 101 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  101 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 101 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 101 126 (Polychromatic418967fa.accept_10_2_1_6_1_634 2 101 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 101 126 (accept_3_4 1 101 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 101 126)))))))))))))))))))))))))) (allB_succ' 27 100 126 (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 100 126 2 13 50 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 100 126 (Polychromatic418967fa.accept_16_9_4_14_1_1878 25 100 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 100 126 2 12 50 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 100 126 (accept_3_5 23 100 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 100 126 2 11 50 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 100 126
  (Polychromatic418967fa.accept_12_9_4_6_1_460 21 100 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 100 126 2 10 50 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 100 126 (Polychromatic418967fa.accept_15_4_10_6_1_2997 19 100 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 100 126 2 9 50 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 100 126 (accept_3_5 17 100 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 100 126 2 8 50 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 100 126
  (Polychromatic418967fa.accept_12_3_4_6_1_434 15 100 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 100 126 2 7 50 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 100 126 (Polychromatic418967fa.accept_19_13_5_12_1_6107 13 100 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 100 126 2 6 50 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 100 126 (accept_3_5 11 100 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 100 126 2 5 50 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 100 126 (Polychromatic418967fa.accept_12_9_4_6_1_460 9
  100 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 100 126 2 4 50 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 100 126
  (Polychromatic418967fa.accept_16_7_4_14_1_2860 7 100 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 100 126 2 3 50 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 100 126 (accept_3_5 5 100 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 100
  126 2 2 50 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  100 126 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 100 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 100 126 2 1 50 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 100 126 (Polychromatic418967fa.accept_15_1_10_6_1_631 1 100 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100 126))))))))))))))))))))))))))) (allB_succ' 28 99 126 (Eq.refl
  Bool.true) (allA_succ_of_gcd 27 99 126 9 3 11 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 26 99 126 (Polychromatic418967fa.accept_12_2_3_6_1_112 26 99 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 25
  99 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 99 126 3 8 33 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 99 126
  (Polychromatic418967fa.accept_10_3_9_6_1_94 23 99 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 99 126 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 99 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 99 126 3 7 33 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 99 126 (Polychromatic418967fa.accept_12_8_3_6_1_909 20 99 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 126
  (Polychromatic418967fa.accept_15_4_9_6_1_627 19 99 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 99 126 9 2 11 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 99 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 99 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 126 (Polychromatic418967fa.accept_12_4_3_6_1_879 16 99 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 99 126 3 5 33 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 99 126
  (Polychromatic418967fa.accept_12_2_3_6_1_112 14 99 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 99 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 99 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 99 126 3 4 33 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 99 126 (Polychromatic418967fa.accept_13_11_8_9_1_1161 11 99 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 126
  (Polychromatic418967fa.accept_12_10_3_6_1_882 10 99 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 99 126 9 1 11 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 99 126 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 99 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 126 (Polychromatic418967fa.accept_13_7_8_9_1_1158 7 99 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 99 126 3 2 33 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 99 126
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 99 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 99 126 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 99 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 99 126 3 1 33 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 99 126 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 99 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 126
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 99 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 99 126)))))))))))))))))))))))))))) (allB_succ' 29 98 126 (Eq.refl Bool.true) (allA_succ_of_gcd 28 98 126 14
  2 7 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 98 126
  (Polychromatic418967fa.accept_12_3_2_6_1_138 27 98 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 98 126 2 13 49 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 98 126 (accept_3_4 25 98 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 98
  126 2 12 49 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  98 126 (Polychromatic418967fa.accept_10_3_8_6_1_326 23 98 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 98 126 2 11 49 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 21 98 126 7 3 14 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 20 98 126 2 10 49 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 98 126 (accept_3_4 19 98 126 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 98 126 2 9 49 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 98 126 (Polychromatic418967fa.accept_11_6_10_5_1_341 17 98 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 98 126 2 8 49 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 98 126 (Polychromatic418967fa.accept_11_4_10_5_1_1202 15 98 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 98 126 14 1 7 9 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 98 126 (accept_3_4 13 98 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 98 126 2 6 49 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 98 126 (Polychromatic418967fa.accept_13_11_7_9_1_612
  11 98 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 98 126 2 5 49 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 98 126
  (Polychromatic418967fa.accept_12_9_2_6_1_455 9 98 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 98 126 2 4 49 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 98 126 7 1 14 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 98 126 2 3 49 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 98 126 (Polychromatic418967fa.accept_22_5_10_16_1_6233 5 98 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 98 126 2 2 49 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 98 126 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 98 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 98 126 2 1 49 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 98 126 (accept_3_4 1 98 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98 126))))))))))))))))))))))))))))) (allB_succ' 30 97 126 (Eq.refl
  Bool.true) (allA_succ_of_accept 29 97 126 (accept_3_5 29 97 126 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 97 126 (Polychromatic418967fa.accept_13_2_6_9_1_2636 28 97 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 97 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 97 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 126 (accept_3_5 26 97 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 126 (Polychromatic418967fa.accept_19_6_2_12_1_6136
  25 97 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 126
  (Polychromatic418967fa.accept_22_2_9_16_1_6269 24 97 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 126 (accept_3_5 23 97 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 126 (Polychromatic418967fa.accept_17_5_12_7_1_2651 22 97 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 126 (Polychromatic418967fa.accept_10_1_7_6_1_91 21 97 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 126 (accept_3_5 20 97 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 97 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 126
  (Polychromatic418967fa.accept_11_7_9_5_1_338 18 97 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 126 (accept_3_5 17 97 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 126 (Polychromatic418967fa.accept_13_3_6_9_1_1150 16 97 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 97 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 126 (accept_3_5 14 97 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 126 (Polychromatic418967fa.accept_10_3_7_6_1_659 13 97 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 126
  (Polychromatic418967fa.accept_15_12_7_6_1_4013 12 97 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 126 (accept_3_5 11 97 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 126 (Polychromatic418967fa.accept_13_10_6_9_1_1152 10 97 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 126 (Polychromatic418967fa.accept_19_9_2_12_1_6243 9 97 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 126 (accept_3_5 8 97 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 97 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 126
  (Polychromatic418967fa.accept_19_6_2_12_1_6136 6 97 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 126 (accept_3_5 5 97 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  126 (Polychromatic418967fa.accept_13_4_6_9_1_3401 4 97 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 97 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 97 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 126 (accept_3_5 2 97 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 97 126 (Polychromatic418967fa.accept_10_1_7_6_1_91 1 97 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97 126)))))))))))))))))))))))))))))) (allB_succ' 31 96
  126 (Eq.refl Bool.true) (allA_succ_of_gcd 30 96 126 6 5 16 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 96 126 (Polychromatic418967fa.accept_13_3_5_9_1_5285 29 96 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 96 126 2 14 48 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 96 126 3 9 32 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 96 126 2 13 48 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 126
  (Polychromatic418967fa.accept_11_3_8_5_1_336 25 96 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 96 126 6 4 16 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 96 126 (Polychromatic418967fa.accept_19_4_1_12_1_4803 23 96 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 96 126 2 11 48 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 96 126 3 7 32 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 96 126 2 10 48 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 96 126 (Polychromatic418967fa.accept_22_19_8_16_1_3106
  19 96 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 126 6 3 16 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 126
  (Polychromatic418967fa.accept_13_4_5_9_1_1829 17 96 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 96 126 2 8 48 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 96 126 3 5 32 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 96 126 2 7 48 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 96 126 (Polychromatic418967fa.accept_11_2_8_5_1_1219 13 96 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 126 6 2 16 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 126 (Polychromatic418967fa.accept_19_11_1_12_1_6237 11 96
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96 126 2 5 48 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 96 126 3 3 32 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 96 126 2 4 48 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 96 126
  (Polychromatic418967fa.accept_19_7_1_12_1_6134 7 96 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 96 126 6 1 16 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 96 126 (Polychromatic418967fa.accept_17_5_11_7_1_6146 5 96 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 126 2 2 48 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 96 126 3 1 32 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 96 126 2 1 48 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 126 (Polychromatic418967fa.accept_13_1_5_9_1_226 1 96 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96 126)))))))))))))))))))))))))))))))
  (allB_succ' 32 95 126 (Eq.refl Bool.true) (allA_succ_of_accept 31 95 126 (accept_3_4 31 95 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 126 (Polychromatic418967fa.accept_20_10_15_6_1_2149 30 95 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 126
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 95 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 126 (accept_3_4 28 95 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 126 (Polychromatic418967fa.accept_15_12_5_6_1_2148 27 95 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 126 (Polychromatic418967fa.accept_15_11_5_6_1_669 26 95 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 126 (accept_3_4 25 95 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 126 (Polychromatic418967fa.accept_10_4_5_6_1_651 24 95 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 126
  (Polychromatic418967fa.accept_16_7_15_14_1_2889 23 95 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 126 (accept_3_4 22 95 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 95 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 126 (Polychromatic418967fa.accept_11_9_7_5_1_749 20 95 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 126 (accept_3_4 19 95 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 126 (Polychromatic418967fa.accept_13_5_4_9_1_601 18 95 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 126
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 95 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 126 (accept_3_4 16 95 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 126 (Polychromatic418967fa.accept_23_15_3_11_1_6268 15 95 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 126 (Polychromatic418967fa.accept_10_4_5_6_1_651 14 95 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 126 (accept_3_4 13 95 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 126 (Polychromatic418967fa.accept_15_12_5_6_1_2148 12 95 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 126
  (Polychromatic418967fa.accept_10_1_5_6_1_649 11 95 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 126 (accept_3_4 10 95 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 95 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 95 126 (Polychromatic418967fa.accept_13_8_4_9_1_1145 8 95 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 126 (accept_3_4 7 95 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 95 126 (Polychromatic418967fa.accept_13_6_4_9_1_4326 6 95 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 95
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 95 126 (accept_3_4 4 95 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95 126 (Polychromatic418967fa.accept_15_3_5_6_1_4005 3
  95 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 126
  (Polychromatic418967fa.accept_25_2_20_1_1_6267 2 95 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 95 126 (accept_3_4 1 95 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95
  126)))))))))))))))))))))))))))))))) (allB_succ' 33 94 126 (Eq.refl Bool.true) (allA_succ_of_gcd 32 94 126 2 16 47 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 94 126
  (Polychromatic418967fa.accept_13_5_3_9_1_1189 31 94 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 94 126 2 15 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 94 126 (accept_3_5 29 94 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 94
  126 2 14 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  94 126 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 94 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 94 126 2 13 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 94 126 (Polychromatic418967fa.accept_10_5_4_6_1_319 25 94 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 94 126 2 12 47 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 94 126 (accept_3_5 23 94 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 94 126 2 11 47 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 94 126
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 94 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 94 126 2 10 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 94 126 (Polychromatic418967fa.accept_13_6_3_9_1_1827 19 94 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 94 126 2 9 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 94 126 (accept_3_5 17 94 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 94 126 2 8 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 94 126 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 94 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 94 126 2 7 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 94 126 (Polychromatic418967fa.accept_15_13_4_6_1_3046
  13 94 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 94 126 2 6 47 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 94 126 (accept_3_5 11
  94 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 94 126 2 5 47 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 94 126
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 94 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 94 126 2 4 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 94 126 (Polychromatic418967fa.accept_13_7_3_9_1_1142 7 94 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 94 126 2 3 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 94 126 (accept_3_5 5 94 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 94 126 2 2 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 94 126 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 94 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 94 126 2 1 47 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 94 126 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1
  94 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94 126)))))))))))))))))))))))))))))))))
  (allB_succ' 34 93 126 (Eq.refl Bool.true) (allA_succ_of_gcd 33 93 126 3 11 31 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 93 126
  (Polychromatic418967fa.accept_12_8_9_6_1_127 32 93 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 93 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 93 126 3 10 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 93 126 (Polychromatic418967fa.accept_10_9_3_6_1_686 29
  93 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 126
  (Polychromatic418967fa.accept_10_8_3_6_1_685 28 93 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 93 126 3 9 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 93 126 (Polychromatic418967fa.accept_12_2_9_6_1_439 26 93 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 126 (Polychromatic418967fa.accept_15_10_3_6_1_3042 25 93
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 93 126 3 8 31 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 93 126
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 93 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 93 126 (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 93 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 93 126 3 7 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 93 126 (Polychromatic418967fa.accept_12_8_9_6_1_127 20 93 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 126
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 93 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 93 126 3 6 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 93 126 (Polychromatic418967fa.accept_10_7_3_6_1_644 17 93 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 126 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 93 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 93 126 3 5 31 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 93 126
  (Polychromatic418967fa.accept_12_2_9_6_1_439 14 93 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 126 (Polychromatic418967fa.accept_23_13_1_11_1_6266 13 93 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 93 126 3 4 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 93 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 93 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 126
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 93 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 93 126 3 3 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 93 126 (Polychromatic418967fa.accept_10_8_3_6_1_685 8 93 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 93 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 93 126 3 2 31 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 93 126
  (Polychromatic418967fa.accept_13_5_2_9_1_1195 5 93 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 93 126 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 93 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 93 126 3 1 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 93 126 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 93 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 126
  (Polychromatic418967fa.accept_13_1_2_9_1_1186 1 93 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 93 126)))))))))))))))))))))))))))))))))) (allB_succ' 35 92 126 (Eq.refl Bool.true) (allA_succ_of_gcd 34 92
  126 2 17 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  92 126 (Polychromatic418967fa.accept_12_9_8_6_1_466 33 92 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 92 126 2 16 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 92 126 (accept_3_4 31 92 126 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 92 126 2 15 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 92 126 (Polychromatic418967fa.accept_27_2_11_18_1_6265 29 92 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 92 126 2 14 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 92 126 (Polychromatic418967fa.accept_12_3_8_6_1_895 27
  92 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 92 126 2 13 46 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 92 126 (accept_3_4 25
  92 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 92 126 2 12 46 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 92 126
  (Polychromatic418967fa.accept_13_10_1_9_1_3380 23 92 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 92 126 2 11 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 92 126 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 92 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 92 126 2 10 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 92 126 (accept_3_4 19 92 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 92 126 2 9 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 92 126 (Polychromatic418967fa.accept_20_17_12_6_1_6171 17 92 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 92 126 2 8 46 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 92 126
  (Polychromatic418967fa.accept_12_3_8_6_1_895 15 92 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 92 126 2 7 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 92 126 (accept_3_4 13 92 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 92
  126 2 6 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  92 126 (Polychromatic418967fa.accept_10_1_2_6_1_638 11 92 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 92 126 2 5 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 92 126 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 92 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 92 126 2 4 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 92 126 (accept_3_4 7 92 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 92 126 2 3 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 92 126 (Polychromatic418967fa.accept_13_5_1_9_1_618 5 92 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 92 126 2 2 46 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 92 126
  (Polychromatic418967fa.accept_12_3_8_6_1_895 3 92 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 92 126 2 1 46 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 92 126 (accept_3_4 1 92 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  126))))))))))))))))))))))))))))))))))) (allB_succ' 36 91 126 (Eq.refl Bool.true) (allA_succ_of_gcd 35 91 126 7 5 13 18
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 91 126
  (Polychromatic418967fa.accept_20_14_11_6_1_6264 34 91 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 91 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 91 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 126 (accept_3_5 32 91 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 91 126 (Polychromatic418967fa.accept_17_14_6_7_1_4980 31 91 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 91 126
  (Polychromatic418967fa.accept_11_8_3_5_1_355 30 91 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 91 126 (accept_3_5 29 91 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 91
  126 7 4 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  91 126 (Polychromatic418967fa.accept_10_7_1_6_1_673 27 91 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 91 126 (accept_3_5 26 91 126 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 91 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 91 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 126 (Polychromatic418967fa.accept_15_9_1_6_1_657 24 91 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 126 (accept_3_5 23 91 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 126 (Polychromatic418967fa.accept_10_2_1_6_1_634
  22 91 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 91 126 7 3 13 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 91 126 (accept_3_5 20
  91 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 126
  (Polychromatic418967fa.accept_11_8_3_5_1_355 19 91 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 91 126 (Polychromatic418967fa.accept_15_3_1_6_1_206 18 91 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 126 (accept_3_5 17 91 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 91 126 (Polychromatic418967fa.accept_17_16_6_7_1_2715 16 91 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 126
  (Polychromatic418967fa.accept_10_5_1_6_1_672 15 91 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 91 126 7 2 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 91 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 91 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 126 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 91 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 126 (accept_3_5 11 91 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 126 (Polychromatic418967fa.accept_15_10_1_6_1_3033
  10 91 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 126
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 91 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 91 126 (accept_3_5 8 91 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 91 126
  7 1 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 91
  126 (Polychromatic418967fa.accept_19_6_15_12_1_6263 6 91 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 91 126 (accept_3_5 5 91 126 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 91 126 (Polychromatic418967fa.accept_25_4_16_1_1_6262 4 91 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 126 (Polychromatic418967fa.accept_15_3_1_6_1_206 3 91 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 126 (accept_3_5 2 91 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 91
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91 126))))))))))))))))))))))))))))))))))))
  (allB_succ' 37 90 126 (Eq.refl Bool.true) (allA_succ_of_gcd 36 90 126 18 2 5 7 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 90 126
  (Polychromatic418967fa.accept_19_16_14_12_1_6261 35 90 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 90 126 2 17 45 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 33 90 126 3 11 30 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 90 126 2 16 45 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 90 126 (Polychromatic418967fa.accept_16_15_10_14_1_2872 31 90 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 126 6 5 15 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 126
  (Polychromatic418967fa.accept_13_3_12_9_1_1193 29 90 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 90 126 2 14 45 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 90 126 9 3 10 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 90 126 2 13 45 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 90 126 (Polychromatic418967fa.accept_19_6_14_12_1_4811 25 90 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 90 126 6 4 15 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 126 (Polychromatic418967fa.accept_13_10_12_9_1_1837 23 90
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 90 126 2 11 45 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 90 126 3 7 30 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 90 126 2 10 45 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 126
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 19 90 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 90 126 18 1 5 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 90 126 (Polychromatic418967fa.accept_19_17_14_12_1_2263 17 90 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 126 2 8 45 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 90 126 3 5 30 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 90 126 2 7 45 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 126 (Polychromatic418967fa.accept_16_13_10_14_1_2871 13 90
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 126 6 2 15 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 126
  (Polychromatic418967fa.accept_17_11_5_7_1_6177 11 90 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 90 126 2 5 45 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 90 126 9 1 10 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 90 126 2 4 45 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 90 126 (Polychromatic418967fa.accept_16_7_10_14_1_1884 7 90 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 126 6 1 15 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90 126 (Polychromatic418967fa.accept_16_5_10_14_1_5074 5 90 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 90 126 2 2 45 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 90 126 3 1 30 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 90 126 2 1 45 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 90 126
  (Polychromatic418967fa.accept_23_1_21_11_1_6260 1 90 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 90 126))))))))))))))))))))))))))))))))))))) (allB_succ' 38 89 126 (Eq.refl Bool.true) (allA_succ_of_accept
  37 89 126 (accept_3_4 37 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 126
  (Polychromatic418967fa.accept_16_4_9_14_1_3883 36 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 89 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 89 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 89 126 (accept_3_4 34 89 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 89 126 (Polychromatic418967fa.accept_10_3_9_6_1_94 33 89 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 89 126
  (Polychromatic418967fa.accept_23_9_20_11_1_4501 32 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 89 126 (accept_3_4 31 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  89 126 (Polychromatic418967fa.accept_19_11_13_12_1_6259 30 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 89 126 (Polychromatic418967fa.accept_17_12_4_7_1_6257 29 89 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 89 126 (accept_3_4 28 89 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 89 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 89 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 89 126
  (Polychromatic418967fa.accept_27_26_8_18_1_6258 26 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 89 126 (accept_3_4 25 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  89 126 (Polychromatic418967fa.accept_15_9_14_6_1_3004 24 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 89 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 89 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 89 126 (accept_3_4 22 89 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 89 126 (Polychromatic418967fa.accept_13_8_11_9_1_593 21 89 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 89 126
  (Polychromatic418967fa.accept_13_7_11_9_1_1858 20 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 89 126 (accept_3_4 19 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  89 126 (Polychromatic418967fa.accept_19_18_13_12_1_4775 18 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 89 126 (Polychromatic418967fa.accept_11_6_1_5_1_2388 17 89 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 89 126 (accept_3_4 16 89 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 89 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 89 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 89 126
  (Polychromatic418967fa.accept_13_1_11_9_1_1857 14 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 89 126 (accept_3_4 13 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  89 126 (Polychromatic418967fa.accept_17_12_4_7_1_6257 12 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 89 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 89 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 89 126 (accept_3_4 10 89 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 89 126 (Polychromatic418967fa.accept_15_9_14_6_1_3004 9 89 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 89 126
  (Polychromatic418967fa.accept_13_8_11_9_1_593 8 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 89 126 (accept_3_4 7 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 89
  126 (Polychromatic418967fa.accept_11_6_1_5_1_2388 6 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 89 126 (Polychromatic418967fa.accept_10_5_9_6_1_697 5 89 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 89 126 (accept_3_4 4 89 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 89 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 89 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 89 126
  (Polychromatic418967fa.accept_13_2_11_9_1_591 2 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 89 126 (accept_3_4 1 89 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 89
  126)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 88 126 (Eq.refl Bool.true) (allA_succ_of_gcd 38 88 126 2 19
  44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 88 126
  (Polychromatic418967fa.accept_15_7_13_6_1_696 37 88 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 88 126 2 18 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 88 126 (accept_3_5 35 88 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 88
  126 2 17 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  88 126 (Polychromatic418967fa.accept_10_3_8_6_1_326 33 88 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 88 126 2 16 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 88 126 (Polychromatic418967fa.accept_23_8_19_11_1_6256 31 88 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 88 126 2 15 44 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 88 126 (accept_3_5 29 88 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 88 126 2 14 44 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 88 126
  (Polychromatic418967fa.accept_12_3_4_6_1_434 27 88 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 88 126 2 13 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 88 126 (Polychromatic418967fa.accept_13_12_10_9_1_1166 25 88 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 88 126 2 12 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 88 126 (accept_3_5 23 88 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 88 126 2 11 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 88 126 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 88 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 88 126 2 10 44 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 88 126
  (Polychromatic418967fa.accept_13_6_10_9_1_4329 19 88 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 88 126 2 9 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 88 126 (accept_3_5 17 88 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 88
  126 2 8 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  88 126 (Polychromatic418967fa.accept_12_3_4_6_1_434 15 88 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 88 126 2 7 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 88 126 (Polychromatic418967fa.accept_10_3_8_6_1_326 13 88 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 88 126 2 6 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 88 126 (accept_3_5 11 88 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 88 126 2 5 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 88 126 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 88 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 88 126 2 4 44 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 88 126
  (Polychromatic418967fa.accept_15_7_13_6_1_696 7 88 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 88 126 2 3 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 88 126 (accept_3_5 5 88 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 88 126
  2 2 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 88
  126 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 88 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 88 126 2 1 44 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 88 126 (Polychromatic418967fa.accept_13_1_10_9_1_215 1 88 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 88 126))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 87 126 (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 87 126 3 13 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 87 126 (Polychromatic418967fa.accept_12_2_3_6_1_112 38 87 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 37
  87 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 87 126 3 12 29 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 87 126
  (Polychromatic418967fa.accept_15_5_12_6_1_639 35 87 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 87 126 (Polychromatic418967fa.accept_12_10_3_6_1_882 34 87 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 87 126 3 11 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 87 126 (Polychromatic418967fa.accept_12_8_3_6_1_909 32
  87 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 126
  (Polychromatic418967fa.accept_10_1_7_6_1_91 31 87 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 87 126 3 10 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 87 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 87 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 126 (Polychromatic418967fa.accept_11_6_10_5_1_341 28 87 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 87 126 3 9 29 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 87 126
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 26 87 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 87 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 87 126 3 8 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 87 126 (Polychromatic418967fa.accept_10_3_7_6_1_659 23 87 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 126
  (Polychromatic418967fa.accept_12_10_3_6_1_882 22 87 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 87 126 3 7 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 87 126 (Polychromatic418967fa.accept_12_8_3_6_1_909 20 87 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 126 (Polychromatic418967fa.accept_20_19_7_6_1_6255 19 87
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 87 126 3 6 29 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 87 126
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 87 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 87 126 (Polychromatic418967fa.accept_12_4_3_6_1_879 16 87 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 87 126 3 5 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 87 126 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 87 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 126
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 87 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 87 126 3 4 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 87 126 (Polychromatic418967fa.accept_10_1_7_6_1_91 11 87 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 126 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 87 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 87 126 3 3 29 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 87 126
  (Polychromatic418967fa.accept_12_8_3_6_1_909 8 87 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 126 (Polychromatic418967fa.accept_15_7_12_6_1_1327 7 87 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 87 126 3 2 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 87 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 87 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 126
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 4 87 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 87 126 3 1 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 87 126 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 87 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 87 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87 126))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 41 86 126 (Eq.refl Bool.true) (allA_succ_of_gcd 40 86 126 2 20 43 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 86 126
  (Polychromatic418967fa.accept_12_3_2_6_1_138 39 86 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 86 126 2 19 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 86 126 (accept_3_4 37 86 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 86
  126 2 18 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  86 126 (Polychromatic418967fa.accept_15_5_11_6_1_692 35 86 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 86 126 2 17 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 86 126 (Polychromatic418967fa.accept_12_9_2_6_1_455 33 86 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 86 126 2 16 43 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 86 126 (accept_3_4 31 86 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 86 126 2 15 43 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 86 126
  (Polychromatic418967fa.accept_11_7_9_5_1_338 29 86 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 86 126 2 14 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 86 126 (Polychromatic418967fa.accept_12_3_2_6_1_138 27 86 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 86 126 2 13 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 86 126 (accept_3_4 25 86 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 86 126 2 12 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 86 126 (Polychromatic418967fa.accept_27_23_5_18_1_6254 23 86
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 86 126 2 11 43 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 86 126
  (Polychromatic418967fa.accept_12_9_2_6_1_455 21 86 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 86 126 2 10 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 86 126 (accept_3_4 19 86 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 86
  126 2 9 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  86 126 (Polychromatic418967fa.accept_13_4_8_9_1_1156 17 86 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 86 126 2 8 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 86 126 (Polychromatic418967fa.accept_12_3_2_6_1_138 15 86 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 86 126 2 7 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 86 126 (accept_3_4 13 86 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 86 126 2 6 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 86 126 (Polychromatic418967fa.accept_13_11_8_9_1_1161 11 86 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 86 126 2 5 43 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 86 126
  (Polychromatic418967fa.accept_12_9_2_6_1_455 9 86 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 86 126 2 4 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 86 126 (accept_3_4 7 86 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 86 126
  2 3 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 86
  126 (Polychromatic418967fa.accept_15_5_11_6_1_692 5 86 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 86 126 2 2 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 86 126 (Polychromatic418967fa.accept_12_3_2_6_1_138 3 86 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 86 126 2 1 43 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 86 126 (accept_3_4 1 86 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 86 126))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 85 126 (Eq.refl
  Bool.true) (allA_succ_of_accept 41 85 126 (accept_3_5 41 85 126 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 85 126 (Polychromatic418967fa.accept_19_2_9_12_1_2237 40 85 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 85 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 85 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 126 (accept_3_5 38 85 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 126 (Polychromatic418967fa.accept_13_11_7_9_1_612
  37 85 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 126
  (Polychromatic418967fa.accept_11_3_8_5_1_336 36 85 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 85 126 (accept_3_5 35 85 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  85 126 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 85 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 85 126 (Polychromatic418967fa.accept_15_3_10_6_1_632 33 85 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 126 (accept_3_5 32 85 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 85 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 85 126
  (Polychromatic418967fa.accept_13_4_7_9_1_5260 30 85 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 85 126 (accept_3_5 29 85 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  85 126 (Polychromatic418967fa.accept_13_2_7_9_1_2616 28 85 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 85 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 85 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 126 (accept_3_5 26 85 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 85 126 (Polychromatic418967fa.accept_11_3_8_5_1_336 25 85 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 126
  (Polychromatic418967fa.accept_10_4_5_6_1_651 24 85 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 85 126 (accept_3_5 23 85 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  85 126 (Polychromatic418967fa.accept_19_3_9_12_1_6253 22 85 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 85 126 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 85 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 126 (accept_3_5 20 85 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 85 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 126
  (Polychromatic418967fa.accept_15_3_10_6_1_632 18 85 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 85 126 (accept_3_5 17 85 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  85 126 (Polychromatic418967fa.accept_13_3_7_9_1_1153 16 85 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 85 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 85 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 126 (accept_3_5 14 85 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 126 (Polychromatic418967fa.accept_11_2_8_5_1_1219 13 85 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 126
  (Polychromatic418967fa.accept_15_12_10_6_1_2134 12 85 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 126 (accept_3_5 11 85 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  85 126 (Polychromatic418967fa.accept_16_10_5_14_1_6173 10 85 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 85 126 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 85 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 126 (accept_3_5 8 85 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 85 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 126
  (Polychromatic418967fa.accept_13_6_7_9_1_1848 6 85 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 126 (accept_3_5 5 85 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  126 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 85 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 85 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 85 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 126 (accept_3_5 2 85 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 126 (Polychromatic418967fa.accept_10_1_5_6_1_649 1 85 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85 126)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 84
  126 (Eq.refl Bool.true) (allA_succ_of_gcd 42 84 126 42 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 126 (Polychromatic418967fa.accept_13_2_6_9_1_2636 41 84 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 84 126 2 20 42 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 84 126 3 13 28 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 84 126 2 19 42 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 84 126
  (Polychromatic418967fa.accept_17_3_16_7_1_5014 37 84 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 84 126 6 6 14 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 84 126 7 5 12 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 34 84 126 2 17 42 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 84 126 3 11 28 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 84 126 2 16 42 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 84 126 (Polychromatic418967fa.accept_11_9_7_5_1_749 31 84 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 126 6 5 14 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 126 (Polychromatic418967fa.accept_13_3_6_9_1_1150 29 84 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 84 126 14 2 6 9 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 84 126 3 9 28 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 84 126 2 13 42 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 126
  (Polychromatic418967fa.accept_10_5_4_6_1_319 25 84 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 84 126 6 4 14 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 84 126 (Polychromatic418967fa.accept_13_10_6_9_1_1152 23 84 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84 126 2 11 42 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 84 126 21 1 4 6 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 84 126 2 10 42 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 84 126 (Polychromatic418967fa.accept_15_4_9_6_1_627 19
  84 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 126 6 3 14 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 126
  (Polychromatic418967fa.accept_13_4_6_9_1_3401 17 84 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 84 126 2 8 42 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 84 126 3 5 28 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 84 126 14 1 6 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 84 126 (Polychromatic418967fa.accept_22_13_18_16_1_1756 13 84 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 126 6 2 14 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 126 (Polychromatic418967fa.accept_15_11_9_6_1_1321 11 84 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 126 2 5 42 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 84 126 3 3 28 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 84 126 2 4 42 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 84 126 7 1 12 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 84 126 6 1 14 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 126
  (Polychromatic418967fa.accept_10_5_4_6_1_319 5 84 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 84 126 2 2 42 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 84 126 3 1 28 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 84 126 2 1 42 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 84 126 (Polychromatic418967fa.accept_13_1_6_9_1_1197 1 84 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 84 126))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 83 126
  (Eq.refl Bool.true) (allA_succ_of_accept 43 83 126 (accept_3_4 43 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 83 126 (Polychromatic418967fa.accept_13_3_5_9_1_5285 42 83 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 83 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 83 126 (accept_3_4 40 83 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 83 126 (Polychromatic418967fa.accept_10_9_3_6_1_686
  39 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 83 126
  (Polychromatic418967fa.accept_10_8_3_6_1_685 38 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 83 126 (accept_3_4 37 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  83 126 (Polychromatic418967fa.accept_17_2_15_7_1_6213 36 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 83 126 (Polychromatic418967fa.accept_19_16_7_12_1_6252 35 83 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 83 126 (accept_3_4 34 83 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 83 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 83 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 83 126
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 32 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 83 126 (accept_3_4 31 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  83 126 (Polychromatic418967fa.accept_13_4_5_9_1_1829 30 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 83 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 83 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 83 126 (accept_3_4 28 83 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 83 126 (Polychromatic418967fa.accept_10_7_3_6_1_644 27 83 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 83 126
  (Polychromatic418967fa.accept_17_9_15_7_1_6212 26 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 83 126 (accept_3_4 25 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  83 126 (Polychromatic418967fa.accept_19_5_7_12_1_2252 24 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 83 126 (Polychromatic418967fa.accept_11_1_6_5_1_1732 23 83 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 83 126 (accept_3_4 22 83 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 83 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 83 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 83 126
  (Polychromatic418967fa.accept_19_1_7_12_1_3443 20 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 83 126 (accept_3_4 19 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  83 126 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 83 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 83 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 83 126 (accept_3_4 16 83 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 83 126 (Polychromatic418967fa.accept_13_2_5_9_1_610 15 83 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 83 126
  (Polychromatic418967fa.accept_13_1_5_9_1_226 14 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 83 126 (accept_3_4 13 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  83 126 (Polychromatic418967fa.accept_11_1_6_5_1_1732 12 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 83 126 (Polychromatic418967fa.accept_16_11_3_14_1_5043 11 83 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 83 126 (accept_3_4 10 83 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 83 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 83 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 83 126
  (Polychromatic418967fa.accept_10_8_3_6_1_685 8 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 83 126 (accept_3_4 7 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 83
  126 (Polychromatic418967fa.accept_25_6_8_1_1_6251 6 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 83 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 83 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 83 126 (accept_3_4 4 83 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 83 126 (Polychromatic418967fa.accept_13_3_5_9_1_5285 3 83 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 126
  (Polychromatic418967fa.accept_13_2_5_9_1_610 2 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 83 126 (accept_3_4 1 83 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 83
  126)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 82 126 (Eq.refl Bool.true) (allA_succ_of_gcd 44 82 126
  2 22 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 82
  126 (Polychromatic418967fa.accept_15_13_7_6_1_682 43 82 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 82 126 2 21 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 82 126 (accept_3_5 41 82 126 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 82 126 2 20 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 82 126 (Polychromatic418967fa.accept_12_3_10_6_1_442 39 82 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 82 126 2 19 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 82 126 (Polychromatic418967fa.accept_19_18_6_12_1_6250
  37 82 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 82 126 2 18 41 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 82 126 (accept_3_5 35
  82 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 82 126 2 17 41 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 82 126
  (Polychromatic418967fa.accept_12_9_10_6_1_872 33 82 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 82 126 2 16 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 82 126 (Polychromatic418967fa.accept_10_1_2_6_1_638 31 82 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 82 126 2 15 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 82 126 (accept_3_5 29 82 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 82 126 2 14 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 82 126 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 82 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 82 126 2 13 41 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 82 126
  (Polychromatic418967fa.accept_17_8_14_7_1_6203 25 82 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 82 126 2 12 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 82 126 (accept_3_5 23 82 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 82
  126 2 11 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  82 126 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 82 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 82 126 2 10 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 82 126 (Polychromatic418967fa.accept_13_6_4_9_1_4326 19 82 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 82 126 2 9 41 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 82 126 (accept_3_5 17 82 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 82 126 2 8 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 82 126 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 82 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 82 126 2 7 41 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 82 126
  (Polychromatic418967fa.accept_15_13_7_6_1_682 13 82 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 82 126 2 6 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 82 126 (accept_3_5 11 82 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 82
  126 2 5 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  82 126 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 82 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 82 126 2 4 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 82 126 (Polychromatic418967fa.accept_13_7_4_9_1_1865 7 82 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 82 126 2 3 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 82 126 (accept_3_5 5 82 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 82 126 2 2 41 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 82 126 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 82 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 82 126 2 1 41 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 82 126
  (Polychromatic418967fa.accept_10_1_2_6_1_638 1 82 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 82 126))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 81 126 (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 81 126 9 5 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 81 126 (Polychromatic418967fa.accept_12_8_9_6_1_127 44 81 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 81 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 81 126 3 14 27 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 81 126
  (Polychromatic418967fa.accept_13_2_3_9_1_2610 41 81 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 126 (Polychromatic418967fa.accept_12_4_9_6_1_440 40 81 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 81 126 3 13 27 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 81 126 (Polychromatic418967fa.accept_12_2_9_6_1_439 38
  81 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 126
  (Polychromatic418967fa.accept_10_7_1_6_1_673 37 81 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 81 126 9 4 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 81 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 81 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 126 (Polychromatic418967fa.accept_12_10_9_6_1_1445 34 81
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 81 126 3 11 27 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 81 126
  (Polychromatic418967fa.accept_10_2_1_6_1_634 32 81 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 81 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 81 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 81 126 3 10 27 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 81 126 (Polychromatic418967fa.accept_16_13_1_14_1_2855
  29 81 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 126
  (Polychromatic418967fa.accept_12_4_9_6_1_440 28 81 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 81 126 9 3 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 81 126 (Polychromatic418967fa.accept_12_2_9_6_1_439 26 81 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 126 (Polychromatic418967fa.accept_10_5_1_6_1_672 25 81 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 81 126 3 8 27 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 81 126
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 81 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 126 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 81 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 81 126 3 7 27 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 81 126 (Polychromatic418967fa.accept_12_8_9_6_1_127 20 81 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 126
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 81 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 81 126 9 2 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 81 126 (Polychromatic418967fa.accept_10_7_1_6_1_673 17 81 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 126 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 81 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 81 126 3 5 27 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 81 126
  (Polychromatic418967fa.accept_12_2_9_6_1_439 14 81 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 126 (Polychromatic418967fa.accept_16_13_1_14_1_2855 13 81 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 81 126 3 4 27 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 81 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 81 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 126
  (Polychromatic418967fa.accept_11_10_4_5_1_359 10 81 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 81 126 9 1 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 81 126 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 81 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 81 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 81 126 3 2 27 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 81 126
  (Polychromatic418967fa.accept_10_5_1_6_1_672 5 81 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 126 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 81 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 81 126 3 1 27 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 81 126 (Polychromatic418967fa.accept_10_2_1_6_1_634 2 81 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 126
  (Polychromatic418967fa.accept_19_1_5_12_1_6249 1 81 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 81 126)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 80 126 (Eq.refl Bool.true)
  (allA_succ_of_gcd 46 80 126 2 23 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 80 126 (Polychromatic418967fa.accept_12_9_8_6_1_466 45 80 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 80 126 2 22 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 80 126 (accept_3_4 43 80 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 80 126 2 21 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 80 126 (Polychromatic418967fa.accept_11_8_3_5_1_355 41 80 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 80 126 2 20 40 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 80 126
  (Polychromatic418967fa.accept_12_3_8_6_1_895 39 80 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 80 126 2 19 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 80 126 (accept_3_4 37 80 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 80
  126 2 18 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  80 126 (Polychromatic418967fa.accept_19_16_4_12_1_6248 35 80 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 80 126 2 17 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 80 126 (Polychromatic418967fa.accept_12_9_8_6_1_466 33 80 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 80 126 2 16 40 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 80 126 (accept_3_4 31 80 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80 126 2 15 40 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 80 126
  (Polychromatic418967fa.accept_13_3_2_9_1_1187 29 80 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 80 126 2 14 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 80 126 (Polychromatic418967fa.accept_12_3_8_6_1_895 27 80 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 80 126 2 13 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 80 126 (accept_3_4 25 80 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 80 126 2 12 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 80 126 (Polychromatic418967fa.accept_31_23_18_2_1_6247 23 80
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 80 126 2 11 40 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 80 126
  (Polychromatic418967fa.accept_12_9_8_6_1_466 21 80 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 80 126 2 10 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 80 126 (accept_3_4 19 80 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 80
  126 2 9 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  80 126 (Polychromatic418967fa.accept_24_17_8_6_1_6246 17 80 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 80 126 2 8 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 80 126 (Polychromatic418967fa.accept_12_3_8_6_1_895 15 80 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 80 126 2 7 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 80 126 (accept_3_4 13 80 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80 126 2 6 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 80 126 (Polychromatic418967fa.accept_13_11_2_9_1_2640 11 80 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 80 126 2 5 40 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 80 126
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 80 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 80 126 2 4 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 80 126 (accept_3_4 7 80 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 80 126
  2 3 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 80
  126 (Polychromatic418967fa.accept_13_5_2_9_1_1195 5 80 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 80 126 2 2 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 80 126 (Polychromatic418967fa.accept_12_3_8_6_1_895 3 80 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 80 126 2 1 40 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 80 126 (accept_3_4 1 80 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 80 126))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 79 126 (Eq.refl
  Bool.true) (allA_succ_of_accept 47 79 126 (accept_3_5 47 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 79 126 (Polychromatic418967fa.accept_22_2_13_16_1_6117 46 79 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 79 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 79 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 126 (accept_3_5 44 79 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 126 (Polychromatic418967fa.accept_10_3_9_6_1_94 43
  79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 126
  (Polychromatic418967fa.accept_16_10_15_14_1_1086 42 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 79 126 (accept_3_5 41 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 79 126 (Polychromatic418967fa.accept_15_10_4_6_1_2129 40 79 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 79 126 (Polychromatic418967fa.accept_15_9_4_6_1_3075 39 79 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 126 (accept_3_5 38 79 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 37
  79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 126
  (Polychromatic418967fa.accept_13_10_1_9_1_3380 36 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 126 (accept_3_5 35 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 126 (Polychromatic418967fa.accept_13_8_1_9_1_1178 34 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 79 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 126 (accept_3_5 32 79 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 126 (Polychromatic418967fa.accept_13_5_1_9_1_618 31 79 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 126
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 30 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 126 (accept_3_5 29 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 126 (Polychromatic418967fa.accept_13_2_1_9_1_1174 28 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 126 (Polychromatic418967fa.accept_20_7_19_6_1_4742 27 79 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 126 (accept_3_5 26 79 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 79 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 126
  (Polychromatic418967fa.accept_13_11_1_9_1_1179 24 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 126 (accept_3_5 23 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 126 (Polychromatic418967fa.accept_17_5_11_7_1_6146 22 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 79 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 126 (accept_3_5 20 79 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 126 (Polychromatic418967fa.accept_11_8_2_5_1_1769 19 79 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 126
  (Polychromatic418967fa.accept_13_5_1_9_1_618 18 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 126 (accept_3_5 17 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 126 (Polychromatic418967fa.accept_25_16_4_1_1_6245 16 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 126 (Polychromatic418967fa.accept_10_5_9_6_1_697 15 79 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 126 (accept_3_5 14 79 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 79 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 126
  (Polychromatic418967fa.accept_24_12_7_6_1_6244 12 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 126 (accept_3_5 11 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 126 (Polychromatic418967fa.accept_13_10_1_9_1_3380 10 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 79 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 126 (accept_3_5 8 79 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 126 (Polychromatic418967fa.accept_16_7_15_14_1_2889 7 79 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 126
  (Polychromatic418967fa.accept_13_6_1_9_1_619 6 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 126 (accept_3_5 5 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  126 (Polychromatic418967fa.accept_16_4_15_14_1_5056 4 79 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 79 126 (Polychromatic418967fa.accept_10_3_9_6_1_94 3 79 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 126 (accept_3_5 2 79 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 79 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 79 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79 126))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 49 78 126 (Eq.refl Bool.true) (allA_succ_of_gcd 48 78 126 6 8 13 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 78 126
  (Polychromatic418967fa.accept_19_9_2_12_1_6243 47 78 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 78 126 2 23 39 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 78 126 3 15 26 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 44 78 126 2 22 39 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 78 126 (Polychromatic418967fa.accept_10_3_8_6_1_326 43 78 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 78 126 6 7 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 78 126 (Polychromatic418967fa.accept_15_11_3_6_1_1306 41 78 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 78 126 2 20 39 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 78 126 3 13 26 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 78 126 2 19 39 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 78 126
  (Polychromatic418967fa.accept_17_3_10_7_1_2646 37 78 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 78 126 6 6 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 78 126 (Polychromatic418967fa.accept_15_5_3_6_1_2128 35 78 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 78 126 2 17 39 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 78 126 3 11 26 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 78 126 2 16 39 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 78 126 (Polychromatic418967fa.accept_15_1_3_6_1_621 31
  78 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 126 6 5 13 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 126
  (Polychromatic418967fa.accept_19_10_2_12_1_6242 29 78 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 78 126 2 14 39 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 78 126 3 9 26 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 78 126 2 13 39 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 78 126 (Polychromatic418967fa.accept_15_10_3_6_1_3042 25 78 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78 126 6 4 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 78 126 (Polychromatic418967fa.accept_10_3_8_6_1_326 23 78 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78 126 2 11 39 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 78 126 3 7 26 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 78 126 2 10 39 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 78 126
  (Polychromatic418967fa.accept_22_19_12_16_1_6241 19 78 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 78 126 6 3 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 78 126 (Polychromatic418967fa.accept_11_6_1_5_1_2388 17 78 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 126 2 8 39 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 78 126 3 5 26 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 78 126 2 7 39 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 126 (Polychromatic418967fa.accept_10_3_8_6_1_326 13
  78 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 126 6 2 13 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 126
  (Polychromatic418967fa.accept_15_11_3_6_1_1306 11 78 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 78 126 2 5 39 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 78 126 3 3 26 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 78 126 2 4 39 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 78 126 (Polychromatic418967fa.accept_22_7_12_16_1_6240 7 78 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 126 6 1 13 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 126 (Polychromatic418967fa.accept_15_5_3_6_1_2128 5 78 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 126 2 2 39 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 78 126 3 1 26 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 78 126 2 1 39 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 126
  (Polychromatic418967fa.accept_15_1_3_6_1_621 1 78 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 78 126))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 77 126 (Eq.refl Bool.true)
  (allA_succ_of_gcd 49 77 126 7 7 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 48 77 126 (Polychromatic418967fa.accept_22_4_11_16_1_6239 48 77 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 77 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 77 126 (accept_3_4 46 77 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 77 126 (Polychromatic418967fa.accept_19_7_1_12_1_6134
  45 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 77 126
  (Polychromatic418967fa.accept_27_17_23_18_1_6238 44 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 77 126 (accept_3_4 43 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 77 126 7 6 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 77 126 (Polychromatic418967fa.accept_10_1_7_6_1_91 41 77 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 77 126 (accept_3_4 40 77 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 77 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 77 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 77 126 (Polychromatic418967fa.accept_15_8_2_6_1_2125
  38 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 126 (accept_3_4 37
  77 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 126
  (Polychromatic418967fa.accept_13_10_12_9_1_1837 36 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 77 126 7 5 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 77 126 (accept_3_4 34 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 126 (Polychromatic418967fa.accept_10_3_7_6_1_659 33 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 126 (Polychromatic418967fa.accept_17_15_9_7_1_3816 32 77 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 126 (accept_3_4 31 77 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 126 (Polychromatic418967fa.accept_19_11_1_12_1_6237 30 77
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 126
  (Polychromatic418967fa.accept_13_3_12_9_1_1193 29 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 77 126 7 4 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 77 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 77 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 77 126 (Polychromatic418967fa.accept_15_11_2_6_1_3010 26 77
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 126 (accept_3_4 25 77 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 126 (Polychromatic418967fa.accept_19_5_1_12_1_6102
  24 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 126
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 126 (accept_3_4 22 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 77
  126 7 3 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20
  77 126 (Polychromatic418967fa.accept_22_20_11_16_1_6236 20 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 77 126 (accept_3_4 19 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 77 126 (Polychromatic418967fa.accept_19_18_1_12_1_6235 18 77 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 126 (Polychromatic418967fa.accept_16_1_13_14_1_1064 17 77
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 77 126 (accept_3_4 16 77 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 77 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 15
  77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 77 126 7 2 11 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 77 126 (accept_3_4 13
  77 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 126
  (Polychromatic418967fa.accept_15_12_2_6_1_2127 12 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 77 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 77 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 77 126 (accept_3_4 10 77 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 77 126 (Polychromatic418967fa.accept_19_9_1_12_1_6234 9 77 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 77 126 (Polychromatic418967fa.accept_13_8_12_9_1_1168
  8 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 77 126 7 1 11 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 77 126
  (Polychromatic418967fa.accept_22_6_11_16_1_6094 6 77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 77 126 (Polychromatic418967fa.accept_17_5_9_7_1_6185 5 77 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 77 126 (accept_3_4 4 77 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 77 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 77 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 77 126 (Polychromatic418967fa.accept_17_2_9_7_1_5002 2
  77 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 126 (accept_3_4 1 77 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 77 126))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 51 76 126 (Eq.refl Bool.true) (allA_succ_of_gcd 50 76 126 2 25 38 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 76 126
  (Polychromatic418967fa.accept_22_5_10_16_1_6233 49 76 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 76 126 2 24 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 76 126 (accept_3_5 47 76 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 76
  126 2 23 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  76 126 (Polychromatic418967fa.accept_12_9_4_6_1_460 45 76 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 76 126 2 22 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 76 126 (Polychromatic418967fa.accept_26_17_24_22_1_6232 43 76 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 76 126 2 21 38 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 76 126 (accept_3_5 41 76 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 76 126 2 20 38 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 76 126
  (Polychromatic418967fa.accept_11_6_10_5_1_341 39 76 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 76 126 2 19 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 76 126 (Polychromatic418967fa.accept_11_4_10_5_1_1202 37 76 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 76 126 2 18 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 76 126 (accept_3_5 35 76 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 76 126 2 17 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 76 126 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 76 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 76 126 2 16 38 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 76 126
  (Polychromatic418967fa.accept_17_14_8_7_1_6183 31 76 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 76 126 2 15 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 76 126 (accept_3_5 29 76 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 76
  126 2 14 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  76 126 (Polychromatic418967fa.accept_12_3_4_6_1_434 27 76 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 76 126 2 13 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 76 126 (Polychromatic418967fa.accept_15_10_1_6_1_3033 25 76 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 76 126 2 12 38 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 76 126 (accept_3_5 23 76 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 76 126 2 11 38 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 76 126
  (Polychromatic418967fa.accept_12_9_4_6_1_460 21 76 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 76 126 2 10 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 76 126 (Polychromatic418967fa.accept_23_19_7_11_1_6231 19 76 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 76 126 2 9 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 76 126 (accept_3_5 17 76 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 76 126 2 8 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 76 126 (Polychromatic418967fa.accept_11_4_10_5_1_1202 15 76 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 76 126 2 7 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 76 126
  (Polychromatic418967fa.accept_27_13_22_18_1_6230 13 76 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 76 126 2 6 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 76 126 (accept_3_5 11 76 126 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 76 126 2 5 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 76 126 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 76 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 76 126 2 4 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 76 126 (Polychromatic418967fa.accept_13_7_11_9_1_1858 7 76 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 76 126 2 3 38 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 76 126 (accept_3_5 5 76 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 76 126 2 2 38 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 76 126 (Polychromatic418967fa.accept_12_3_4_6_1_434 3
  76 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 76 126 2 1 38 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 76 126
  (Polychromatic418967fa.accept_13_1_11_9_1_1857 1 76 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 76 126))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 75 126 (Eq.refl Bool.true)
  (allA_succ_of_gcd 51 75 126 3 17 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 75 126 (Polychromatic418967fa.accept_12_2_3_6_1_112 50 75 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 75 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 75 126 3 16 25 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 75 126
  (Polychromatic418967fa.accept_19_9_18_12_1_2286 47 75 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 75 126 (Polychromatic418967fa.accept_12_10_3_6_1_882 46 75 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75 126 3 15 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 75 126 (Polychromatic418967fa.accept_10_4_5_6_1_651 44
  75 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 126
  (Polychromatic418967fa.accept_23_20_6_11_1_6229 43 75 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 75 126 3 14 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 75 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 75 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 126 (Polychromatic418967fa.accept_11_7_9_5_1_338 40 75 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 75 126 3 13 25 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 75 126
  (Polychromatic418967fa.accept_12_2_3_6_1_112 38 75 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 75 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 75 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 75 126 3 12 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 75 126 (Polychromatic418967fa.accept_16_3_11_14_1_446
  35 75 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 126
  (Polychromatic418967fa.accept_10_4_5_6_1_651 34 75 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 75 126 3 11 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 75 126 (Polychromatic418967fa.accept_12_8_3_6_1_909 32 75 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 126 (Polychromatic418967fa.accept_10_1_5_6_1_649 31 75 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 75 126 3 10 25 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 75 126
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 75 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 75 126 (Polychromatic418967fa.accept_12_4_3_6_1_879 28 75 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 75 126 3 9 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 75 126 (Polychromatic418967fa.accept_12_2_3_6_1_112 26 75 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 126
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 75 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 75 126 3 8 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 75 126 (Polychromatic418967fa.accept_27_23_21_18_1_6228 23 75 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 126 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 75 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 75 126 3 7 25 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 75 126
  (Polychromatic418967fa.accept_12_8_3_6_1_909 20 75 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 75 126 (Polychromatic418967fa.accept_10_9_5_6_1_691 19 75 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 75 126 3 6 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 75 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 75 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 126
  (Polychromatic418967fa.accept_12_4_3_6_1_879 16 75 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 75 126 3 5 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 75 126 (Polychromatic418967fa.accept_10_4_5_6_1_651 14 75 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 75 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 75 126 3 4 25 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 75 126
  (Polychromatic418967fa.accept_10_1_5_6_1_649 11 75 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 75 126 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 75 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 75 126 3 3 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 75 126 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 75 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 126
  (Polychromatic418967fa.accept_11_7_9_5_1_338 7 75 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 75 126 3 2 25 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 75 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 75 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 126 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 75 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 75 126 3 1 25 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 75 126
  (Polychromatic418967fa.accept_12_2_3_6_1_112 2 75 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 75 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 75 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 75 126)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 74
  126 (Eq.refl Bool.true) (allA_succ_of_gcd 52 74 126 2 26 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 74 126 (Polychromatic418967fa.accept_12_3_2_6_1_138 51 74 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 74 126 2 25 37 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 74 126 (accept_3_4 49
  74 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 74 126 2 24 37 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 74 126
  (Polychromatic418967fa.accept_11_3_8_5_1_336 47 74 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 74 126 2 23 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 74 126 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 74 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 74 126 2 22 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 74 126 (accept_3_4 43 74 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 74 126 2 21 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 74 126 (Polychromatic418967fa.accept_19_3_17_12_1_6176 41 74
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 74 126 2 20 37 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 74 126
  (Polychromatic418967fa.accept_12_3_2_6_1_138 39 74 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 74 126 2 19 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 74 126 (accept_3_4 37 74 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 74
  126 2 18 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  74 126 (Polychromatic418967fa.accept_10_5_4_6_1_319 35 74 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 74 126 2 17 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 74 126 (Polychromatic418967fa.accept_12_9_2_6_1_455 33 74 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 74 126 2 16 37 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 74 126 (accept_3_4 31 74 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 74 126 2 15 37 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 74 126
  (Polychromatic418967fa.accept_16_13_10_14_1_2871 29 74 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 74 126 2 14 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 74 126 (Polychromatic418967fa.accept_12_3_2_6_1_138 27 74 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 74 126 2 13 37 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 74 126 (accept_3_4 25 74 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 74 126 2 12 37 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 74 126
  (Polychromatic418967fa.accept_15_8_14_6_1_3003 23 74 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 74 126 2 11 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 74 126 (Polychromatic418967fa.accept_12_9_2_6_1_455 21 74 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 74 126 2 10 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 74 126 (accept_3_4 19 74 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 74 126 2 9 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 74 126 (Polychromatic418967fa.accept_23_17_5_11_1_6227 17 74 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 74 126 2 8 37 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 74 126
  (Polychromatic418967fa.accept_10_5_4_6_1_319 15 74 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 74 126 2 7 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 74 126 (accept_3_4 13 74 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74
  126 2 6 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  74 126 (Polychromatic418967fa.accept_20_11_14_6_1_4714 11 74 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 74 126 2 5 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 74 126 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 74 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 74 126 2 4 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 74 126 (accept_3_4 7 74 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 74 126 2 3 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 74 126 (Polychromatic418967fa.accept_10_5_4_6_1_319 5 74 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 74 126 2 2 37 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 74 126
  (Polychromatic418967fa.accept_11_3_8_5_1_336 3 74 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 74 126 2 1 37 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 74 126 (accept_3_4 1 74 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  126))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 73 126 (Eq.refl Bool.true)
  (allA_succ_of_accept 53 73 126 (accept_3_5 53 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 126 (Polychromatic418967fa.accept_15_7_13_6_1_696 52 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 73 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 126 (accept_3_5 50 73 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 126 (Polychromatic418967fa.accept_10_9_3_6_1_686 49 73 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 126
  (Polychromatic418967fa.accept_10_8_3_6_1_685 48 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 126 (accept_3_5 47 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 126 (Polychromatic418967fa.accept_13_7_8_9_1_1158 46 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 126 (Polychromatic418967fa.accept_17_11_5_7_1_6177 45 73 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 126 (accept_3_5 44 73 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 73 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 126
  (Polychromatic418967fa.accept_11_9_7_5_1_749 42 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 126 (accept_3_5 41 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 126 (Polychromatic418967fa.accept_13_1_8_9_1_1154 40 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 73 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 126 (accept_3_5 38 73 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 126 (Polychromatic418967fa.accept_10_7_3_6_1_644 37 73 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 126
  (Polychromatic418967fa.accept_16_4_9_14_1_3883 36 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 126 (accept_3_5 35 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 126 (Polychromatic418967fa.accept_15_4_13_6_1_642 34 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 126 (Polychromatic418967fa.accept_13_7_8_9_1_1158 33 73 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 126 (accept_3_5 32 73 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 73 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 126
  (Polychromatic418967fa.accept_13_4_8_9_1_1156 30 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 126 (accept_3_5 29 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 126 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 73 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 126 (accept_3_5 26 73 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 126 (Polychromatic418967fa.accept_13_12_8_9_1_1833 25 73 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 126
  (Polychromatic418967fa.accept_13_11_8_9_1_1161 24 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 126 (accept_3_5 23 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 126 (Polychromatic418967fa.accept_15_7_13_6_1_696 22 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 126 (Polychromatic418967fa.accept_16_5_9_14_1_5051 21 73 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 126 (accept_3_5 20 73 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 73 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 126
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 126 (accept_3_5 17 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 126 (Polychromatic418967fa.accept_13_3_8_9_1_1134 16 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 73 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 126 (accept_3_5 14 73 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 126 (Polychromatic418967fa.accept_19_13_16_12_1_6096 13 73 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 126
  (Polychromatic418967fa.accept_13_12_8_9_1_1833 12 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 126 (accept_3_5 11 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 126 (Polychromatic418967fa.accept_22_10_7_16_1_6226 10 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 126 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 73 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 126 (accept_3_5 8 73 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 73 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 126
  (Polychromatic418967fa.accept_19_6_16_12_1_6118 6 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 126 (accept_3_5 5 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  126 (Polychromatic418967fa.accept_13_4_8_9_1_1156 4 73 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 73 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 73 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 126 (accept_3_5 2 73 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 126 (Polychromatic418967fa.accept_13_1_8_9_1_1154 1 73 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  126)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 72 126 (Eq.refl Bool.true) (allA_succ_of_gcd
  54 72 126 18 3 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 72 126 (Polychromatic418967fa.accept_22_9_6_16_1_6225 53 72 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 72 126 2 26 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 72 126 3 17 24 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 72 126 2 25 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 72 126
  (Polychromatic418967fa.accept_26_23_20_22_1_6224 49 72 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 72 126 6 8 12 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 72 126 (Polychromatic418967fa.accept_13_8_7_9_1_611 47 72 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 72 126 2 23 36 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 72 126 9 5 8 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 72 126 2 22 36 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 72 126
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 43 72 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 72 126 6 7 12 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 72 126 (Polychromatic418967fa.accept_10_1_2_6_1_638 41 72 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 72 126 2 20 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 72 126 3 13 24 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 72 126 2 19 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 126 (Polychromatic418967fa.accept_13_11_7_9_1_612
  37 72 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 126 18 2 4 7 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 126
  (Polychromatic418967fa.accept_15_5_12_6_1_639 35 72 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 72 126 2 17 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 72 126 3 11 24 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 72 126 2 16 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 72 126 (Polychromatic418967fa.accept_10_1_2_6_1_638 31 72 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 126 6 5 12 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 126 (Polychromatic418967fa.accept_13_3_7_9_1_1153 29 72 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 72 126 2 14 36 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 72 126 9 3 8 14 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 72 126 2 13 36 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 126
  (Polychromatic418967fa.accept_15_10_12_6_1_3000 25 72 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 72 126 6 4 12 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 72 126 (Polychromatic418967fa.accept_11_1_6_5_1_1732 23 72 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72 126 2 11 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 72 126 3 7 24 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 72 126 2 10 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 72 126 (Polychromatic418967fa.accept_13_6_7_9_1_1848
  19 72 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72 126 18 1 4 7 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 72 126
  (Polychromatic418967fa.accept_13_4_7_9_1_5260 17 72 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 72 126 2 8 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 72 126 3 5 24 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 72 126 2 7 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 72 126 (Polychromatic418967fa.accept_22_13_6_16_1_6223 13 72 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 126 6 2 12 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 126 (Polychromatic418967fa.accept_10_1_2_6_1_638 11 72 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 126 2 5 36 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 72 126 9 1 8 14 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 72 126 2 4 36 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 72 126
  (Polychromatic418967fa.accept_15_7_12_6_1_1327 7 72 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 72 126 6 1 12 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 72 126 (Polychromatic418967fa.accept_15_5_12_6_1_639 5 72 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 126 2 2 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 72 126 3 1 24 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 72 126 2 1 36 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 126 (Polychromatic418967fa.accept_10_1_2_6_1_638 1 72 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  126))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 71 126 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 71 126 (accept_3_4 55 71 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  71 126 (Polychromatic418967fa.accept_13_2_6_9_1_2636 54 71 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 71 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 71 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 71 126 (accept_3_4 52 71 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 71 126 (Polychromatic418967fa.accept_19_13_14_12_1_4797 51 71 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 71 126
  (Polychromatic418967fa.accept_15_5_11_6_1_692 50 71 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 71 126 (accept_3_4 49 71 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  71 126 (Polychromatic418967fa.accept_15_3_11_6_1_3083 48 71 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 71 126 (Polychromatic418967fa.accept_10_7_1_6_1_673 47 71 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 71 126 (accept_3_4 46 71 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 71 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 71 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 71 126
  (Polychromatic418967fa.accept_17_10_3_7_1_1679 44 71 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 71 126 (accept_3_4 43 71 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  71 126 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 71 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 71 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 71 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 71 126 (accept_3_4 40 71 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 71 126 (Polychromatic418967fa.accept_15_9_11_6_1_637 39 71 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 71 126
  (Polychromatic418967fa.accept_17_4_3_7_1_4971 38 71 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 71 126 (accept_3_4 37 71 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  71 126 (Polychromatic418967fa.accept_13_10_6_9_1_1152 36 71 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 71 126 (Polychromatic418967fa.accept_10_5_1_6_1_672 35 71 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 71 126 (accept_3_4 34 71 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 71 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 71 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 71 126
  (Polychromatic418967fa.accept_10_2_1_6_1_634 32 71 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 71 126 (accept_3_4 31 71 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  71 126 (Polychromatic418967fa.accept_13_4_6_9_1_3401 30 71 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 71 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 71 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 71 126 (accept_3_4 28 71 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 71 126 (Polychromatic418967fa.accept_10_7_1_6_1_673 27 71 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 71 126
  (Polychromatic418967fa.accept_16_10_7_14_1_2882 26 71 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 71 126 (accept_3_4 25 71 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  71 126 (Polychromatic418967fa.accept_15_9_11_6_1_637 24 71 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 71 126 (Polychromatic418967fa.accept_13_10_6_9_1_1152 23 71 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 71 126 (accept_3_4 22 71 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 71 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 71 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 71 126
  (Polychromatic418967fa.accept_13_7_6_9_1_1831 20 71 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 71 126 (accept_3_4 19 71 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  71 126 (Polychromatic418967fa.accept_15_3_11_6_1_3083 18 71 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 71 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 71 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 71 126 (accept_3_4 16 71 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 71 126 (Polychromatic418967fa.accept_10_5_1_6_1_672 15 71 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 71 126
  (Polychromatic418967fa.accept_13_1_6_9_1_1197 14 71 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 71 126 (accept_3_4 13 71 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  71 126 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 71 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 71 126 (Polychromatic418967fa.accept_22_11_5_16_1_6222 11 71 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 71 126 (accept_3_4 10 71 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 71 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 71 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 126
  (Polychromatic418967fa.accept_25_8_21_1_1_6221 8 71 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 71 126 (accept_3_4 7 71 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71
  126 (Polychromatic418967fa.accept_19_6_14_12_1_4811 6 71 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 71 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 71 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 71 126 (accept_3_4 4 71 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 71 126 (Polychromatic418967fa.accept_13_3_6_9_1_1150 3 71 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 126
  (Polychromatic418967fa.accept_10_2_1_6_1_634 2 71 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 71 126 (accept_3_4 1 71 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 71
  126)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 70 126 (Eq.refl Bool.true)
  (allA_succ_of_gcd 56 70 126 14 4 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 70 126 (Polychromatic418967fa.accept_13_3_5_9_1_5285 55 70 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 70 126 2 27 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 70 126 (accept_3_5 53 70 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 70 126 2 26 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 70 126 (Polychromatic418967fa.accept_12_3_10_6_1_442 51 70 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 70 126 2 25 35 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 49 70 126 7 7 10 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 70 126 2 24 35 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 70 126 (accept_3_5 47
  70 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 70 126 2 23 35 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 70 126
  (Polychromatic418967fa.accept_12_9_10_6_1_872 45 70 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 70 126 2 22 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 70 126 (Polychromatic418967fa.accept_11_10_4_5_1_359 43 70 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 70 126 14 3 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 70 126 (accept_3_5 41 70 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 70 126 2 20 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 70 126 (Polychromatic418967fa.accept_12_3_10_6_1_442 39 70 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 70 126 2 19 35 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 70 126
  (Polychromatic418967fa.accept_19_18_13_12_1_4775 37 70 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 70 126 2 18 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 35 70 126 7 5 10 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 34 70 126 2 17 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 70 126 (Polychromatic418967fa.accept_12_9_10_6_1_872 33 70 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 70 126 2 16 35 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 70 126
  (Polychromatic418967fa.accept_15_1_10_6_1_631 31 70 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 70 126 2 15 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 70 126 (accept_3_5 29 70 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 70
  126 14 2 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  70 126 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 70 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 70 126 2 13 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 70 126 (Polychromatic418967fa.accept_19_6_13_12_1_6220 25 70 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 70 126 2 12 35 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 70 126 (accept_3_5 23 70 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 70 126 2 11 35 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 70 126 7 3 10 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 70 126 2 10 35 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 70 126
  (Polychromatic418967fa.accept_15_4_10_6_1_2997 19 70 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 70 126 2 9 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 70 126 (accept_3_5 17 70 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 70
  126 2 8 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  70 126 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 70 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 70 126 14 1 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 70 126 (Polychromatic418967fa.accept_17_13_2_7_1_6122 13 70 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 70 126 2 6 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 70 126 (accept_3_5 11 70 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70 126 2 5 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 70 126 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 70 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 70 126 2 4 35 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 70 126 7 1 10 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 70 126 2 3 35 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 70 126 (accept_3_5 5 70 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 70 126 2 2 35 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 70 126 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 70 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 70 126 2 1 35 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 70 126
  (Polychromatic418967fa.accept_13_1_5_9_1_226 1 70 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 70 126))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 69 126 (Eq.refl Bool.true)
  (allA_succ_of_gcd 57 69 126 3 19 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 69 126 (Polychromatic418967fa.accept_12_8_9_6_1_127 56 69 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 69 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 69 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 69 126 3 18 23 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 69 126
  (Polychromatic418967fa.accept_10_3_9_6_1_94 53 69 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 69 126 (Polychromatic418967fa.accept_11_8_3_5_1_355 52 69 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 69 126 3 17 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 69 126 (Polychromatic418967fa.accept_12_2_9_6_1_439 50
  69 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 126
  (Polychromatic418967fa.accept_15_4_9_6_1_627 49 69 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 69 126 3 16 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 69 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 69 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 126 (Polychromatic418967fa.accept_12_10_9_6_1_1445 46 69
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 69 126 3 15 23 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 69 126
  (Polychromatic418967fa.accept_12_8_9_6_1_127 44 69 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 69 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 69 126 3 14 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 69 126 (Polychromatic418967fa.accept_11_8_3_5_1_355 41
  69 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 126
  (Polychromatic418967fa.accept_12_4_9_6_1_440 40 69 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 69 126 3 13 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 69 126 (Polychromatic418967fa.accept_12_2_9_6_1_439 38 69 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 126 (Polychromatic418967fa.accept_20_17_9_6_1_6219 37 69
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 69 126 3 12 23 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 69 126
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 69 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 69 126 (Polychromatic418967fa.accept_12_10_9_6_1_1445 34 69 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 69 126 3 11 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 69 126 (Polychromatic418967fa.accept_12_8_9_6_1_127 32
  69 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 126
  (Polychromatic418967fa.accept_4_3_1_2_1_62 31 69 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 69 126 3 10 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 69 126 (Polychromatic418967fa.accept_15_14_9_6_1_5093 29 69 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 126 (Polychromatic418967fa.accept_12_4_9_6_1_440 28 69 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 69 126 3 9 23 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 69 126
  (Polychromatic418967fa.accept_12_2_9_6_1_439 26 69 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 126 (Polychromatic418967fa.accept_10_5_9_6_1_697 25 69 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 69 126 3 8 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 69 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 69 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 126
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 69 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 69 126 3 7 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 69 126 (Polychromatic418967fa.accept_12_8_9_6_1_127 20 69 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 69 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 69 126 3 6 23 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 69 126
  (Polychromatic418967fa.accept_20_17_9_6_1_6219 17 69 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 69 126 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 69 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 69 126 3 5 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 69 126 (Polychromatic418967fa.accept_12_2_9_6_1_439 14 69 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 126
  (Polychromatic418967fa.accept_10_3_9_6_1_94 13 69 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 69 126 3 4 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 69 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 69 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 126 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 69
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 69 126 3 3 23 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 69 126
  (Polychromatic418967fa.accept_11_8_3_5_1_355 8 69 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 69 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 69 126 3 2 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 69 126 (Polychromatic418967fa.accept_10_5_9_6_1_697 5 69 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 126
  (Polychromatic418967fa.accept_12_4_9_6_1_440 4 69 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 69 126 3 1 23 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 69 126 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 69 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 126 (Polychromatic418967fa.accept_15_1_9_6_1_1323 1 69 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  126)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 68 126 (Eq.refl Bool.true)
  (allA_succ_of_gcd 58 68 126 2 29 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 68 126 (Polychromatic418967fa.accept_12_9_8_6_1_466 57 68 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 68 126 2 28 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 68 126 (accept_3_4 55 68 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 68 126 2 27 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 68 126 (Polychromatic418967fa.accept_10_3_8_6_1_326 53 68 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 68 126 2 26 34 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 68 126
  (Polychromatic418967fa.accept_12_3_8_6_1_895 51 68 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 68 126 2 25 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 68 126 (accept_3_4 49 68 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 68
  126 2 24 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  68 126 (Polychromatic418967fa.accept_13_8_3_9_1_5269 47 68 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 68 126 2 23 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 68 126 (Polychromatic418967fa.accept_12_9_8_6_1_466 45 68 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 68 126 2 22 34 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 68 126 (accept_3_4 43 68 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 68 126 2 21 34 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 68 126
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 41 68 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 68 126 2 20 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 68 126 (Polychromatic418967fa.accept_12_3_8_6_1_895 39 68 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 68 126 2 19 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 68 126 (accept_3_4 37 68 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 68 126 2 18 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 68 126 (Polychromatic418967fa.accept_22_13_2_16_1_6151 35 68
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 68 126 2 17 34 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 68 126
  (Polychromatic418967fa.accept_10_3_8_6_1_326 33 68 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 68 126 2 16 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 68 126 (accept_3_4 31 68 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 68
  126 2 15 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  68 126 (Polychromatic418967fa.accept_15_14_8_6_1_2133 29 68 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 68 126 2 14 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 68 126 (Polychromatic418967fa.accept_12_3_8_6_1_895 27 68 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 68 126 2 13 34 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 68 126 (accept_3_4 25 68 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 68 126 2 12 34 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 68 126
  (Polychromatic418967fa.accept_10_3_8_6_1_326 23 68 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 68 126 2 11 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 68 126 (Polychromatic418967fa.accept_12_9_8_6_1_466 21 68 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 68 126 2 10 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 68 126 (accept_3_4 19 68 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 68 126 2 9 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 68 126 (Polychromatic418967fa.accept_15_2_8_6_1_1340 17 68 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 68 126 2 8 34 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 68 126
  (Polychromatic418967fa.accept_12_3_8_6_1_895 15 68 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 68 126 2 7 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 68 126 (accept_3_4 13 68 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68
  126 2 6 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  68 126 (Polychromatic418967fa.accept_22_11_2_16_1_759 11 68 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 68 126 2 5 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 68 126 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 68 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 68 126 2 4 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 68 126 (accept_3_4 7 68 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 126 2 3 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 68 126 (Polychromatic418967fa.accept_13_5_3_9_1_1189 5 68 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 68 126 2 2 34 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 68 126
  (Polychromatic418967fa.accept_10_3_8_6_1_326 3 68 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 68 126 2 1 34 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 68 126 (accept_3_4 1 68 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  126))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 67 126 (Eq.refl Bool.true)
  (allA_succ_of_accept 59 67 126 (accept_3_5 59 67 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 126 (Polychromatic418967fa.accept_13_6_2_9_1_1188 58 67 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 67 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 126 (accept_3_5 56 67 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 126 (Polychromatic418967fa.accept_13_3_2_9_1_1187 55 67 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 126
  (Polychromatic418967fa.accept_17_3_16_7_1_5014 54 67 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 126 (accept_3_5 53 67 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 126 (Polychromatic418967fa.accept_19_14_10_12_1_4809 52 67 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 126 (Polychromatic418967fa.accept_10_1_7_6_1_91 51 67 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 126 (accept_3_5 50 67 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 67 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 126
  (Polychromatic418967fa.accept_23_2_21_11_1_6218 48 67 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 126 (accept_3_5 47 67 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 126 (Polychromatic418967fa.accept_13_7_2_9_1_1826 46 67 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 67 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 126 (accept_3_5 44 67 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 126 (Polychromatic418967fa.accept_10_3_7_6_1_659 43 67 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 126
  (Polychromatic418967fa.accept_13_3_2_9_1_1187 42 67 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 126 (accept_3_5 41 67 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 126 (Polychromatic418967fa.accept_13_1_2_9_1_1186 40 67 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 126 (Polychromatic418967fa.accept_11_6_1_5_1_2388 39 67 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 126 (accept_3_5 38 67 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 67 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 126
  (Polychromatic418967fa.accept_19_17_10_12_1_6157 36 67 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 67 126 (accept_3_5 35 67 126 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 67 126 (Polychromatic418967fa.accept_22_12_1_16_1_3122 34 67 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 67 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 67 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 126 (accept_3_5 32 67 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 126 (Polychromatic418967fa.accept_10_1_7_6_1_91 31
  67 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 126
  (Polychromatic418967fa.accept_19_11_10_12_1_2256 30 67 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 67 126 (accept_3_5 29 67 126 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 67 126 (Polychromatic418967fa.accept_11_6_1_5_1_2388 28 67 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 67 126 (Polychromatic418967fa.accept_13_1_2_9_1_1186 27 67 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 126 (accept_3_5 26 67 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 25
  67 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 126
  (Polychromatic418967fa.accept_13_11_2_9_1_2640 24 67 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 126 (accept_3_5 23 67 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 126 (Polychromatic418967fa.accept_19_3_10_12_1_6217 22 67 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 67 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 126 (accept_3_5 20 67 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 126 (Polychromatic418967fa.accept_13_6_2_9_1_1188 19 67 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 126
  (Polychromatic418967fa.accept_13_5_2_9_1_1195 18 67 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 126 (accept_3_5 17 67 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 126 (Polychromatic418967fa.accept_13_3_2_9_1_1187 16 67 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 126 (Polychromatic418967fa.accept_22_15_1_16_1_6216 15 67 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 126 (accept_3_5 14 67 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 67 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 126
  (Polychromatic418967fa.accept_15_12_7_6_1_4013 12 67 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 126 (accept_3_5 11 67 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 126 (Polychromatic418967fa.accept_17_10_16_7_1_6215 10 67 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 67 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 126 (accept_3_5 8 67 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 126 (Polychromatic418967fa.accept_13_7_2_9_1_1826 7 67 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 126
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 6 67 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 126 (accept_3_5 5 67 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  126 (Polychromatic418967fa.accept_27_4_13_18_1_6214 4 67 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 67 126 (Polychromatic418967fa.accept_10_3_7_6_1_659 3 67 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 126 (accept_3_5 2 67 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 67 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  126)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 66 126 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 66 126 6 10 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 66 126 (Polychromatic418967fa.accept_19_2_9_12_1_2237 59 66 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 126 2 29 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 66 126 3 19 22 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 66 126 2 28 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 66 126 (Polychromatic418967fa.accept_23_9_20_11_1_4501
  55 66 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 66 126 6 9 11 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 66 126
  (Polychromatic418967fa.accept_17_2_15_7_1_6213 53 66 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 66 126 2 26 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 51 66 126 3 17 22 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 50 66 126 2 25 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 66 126 (Polychromatic418967fa.accept_13_10_1_9_1_3380 49 66 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 126 6 8 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 126 (Polychromatic418967fa.accept_13_8_1_9_1_1178 47 66 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 66 126 2 23 33 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 66 126 3 15 22 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 66 126 2 22 33 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 66 126
  (Polychromatic418967fa.accept_17_9_15_7_1_6212 43 66 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 66 126 6 7 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 66 126 (Polychromatic418967fa.accept_13_2_1_9_1_1174 41 66 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 126 2 20 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 66 126 3 13 22 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 66 126 2 19 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 66 126 (Polychromatic418967fa.accept_13_11_1_9_1_1179
  37 66 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66 126 6 6 11 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 66 126
  (Polychromatic418967fa.accept_19_16_9_12_1_4792 35 66 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 66 126 2 17 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 66 126 3 11 22 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 66 126 2 16 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 66 126 (Polychromatic418967fa.accept_13_5_1_9_1_618 31 66 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 126 6 5 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 126 (Polychromatic418967fa.accept_19_10_9_12_1_4774 29 66
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66 126 2 14 33 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 66 126 3 9 22 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 66 126 2 13 33 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 66 126
  (Polychromatic418967fa.accept_24_1_18_6_1_6211 25 66 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 66 126 6 4 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 66 126 (Polychromatic418967fa.accept_13_10_1_9_1_3380 23 66 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 126 2 11 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 66 126 3 7 22 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 66 126 2 10 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 126 (Polychromatic418967fa.accept_13_6_1_9_1_619 19
  66 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 126 6 3 11 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 126
  (Polychromatic418967fa.accept_24_17_18_6_1_6210 17 66 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 66 126 2 8 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 66 126 3 5 22 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 66 126 2 7 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 66 126 (Polychromatic418967fa.accept_24_13_18_6_1_6209 13 66 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 126 6 2 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 126 (Polychromatic418967fa.accept_13_11_1_9_1_1179 11 66 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66 126 2 5 33 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 66 126 3 3 22 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 66 126 2 4 33 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 126
  (Polychromatic418967fa.accept_24_7_18_6_1_6208 7 66 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 66 126 6 1 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 66 126 (Polychromatic418967fa.accept_13_5_1_9_1_618 5 66 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 126 2 2 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 66 126 3 1 22 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 66 126 2 1 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 126 (Polychromatic418967fa.accept_19_1_9_12_1_6207 1 66 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  126))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 65 126 (Eq.refl Bool.true)
  (allA_succ_of_accept 61 65 126 (accept_3_4 61 65 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  65 126 (Polychromatic418967fa.accept_24_12_17_6_1_6206 60 65 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 65 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 65 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 65 126 (accept_3_4 58 65 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 65 126 (Polychromatic418967fa.accept_15_12_5_6_1_2148 57 65 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 65 126
  (Polychromatic418967fa.accept_15_11_5_6_1_669 56 65 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 65 126 (accept_3_4 55 65 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  65 126 (Polychromatic418967fa.accept_10_4_5_6_1_651 54 65 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 65 126 (Polychromatic418967fa.accept_19_15_8_12_1_1286 53 65 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 65 126 (accept_3_4 52 65 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 65 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 65 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 65 126
  (Polychromatic418967fa.accept_11_6_10_5_1_341 50 65 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 65 126 (accept_3_4 49 65 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  65 126 (Polychromatic418967fa.accept_11_4_10_5_1_1202 48 65 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 65 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 65 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 65 126 (accept_3_4 46 65 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 65 126 (Polychromatic418967fa.accept_16_13_1_14_1_2855 45 65 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 65 126
  (Polychromatic418967fa.accept_10_4_5_6_1_651 44 65 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 65 126 (accept_3_4 43 65 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  65 126 (Polychromatic418967fa.accept_15_12_5_6_1_2148 42 65 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 65 126 (Polychromatic418967fa.accept_10_1_5_6_1_649 41 65 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 65 126 (accept_3_4 40 65 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 65 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 65 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 65 126
  (Polychromatic418967fa.accept_17_4_14_7_1_4965 38 65 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 65 126 (accept_3_4 37 65 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  65 126 (Polychromatic418967fa.accept_16_4_1_14_1_3908 36 65 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 65 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 65 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 65 126 (accept_3_4 34 65 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 126 (Polychromatic418967fa.accept_15_3_5_6_1_4005 33 65 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 65 126
  (Polychromatic418967fa.accept_20_12_5_6_1_6205 32 65 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 65 126 (accept_3_4 31 65 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  65 126 (Polychromatic418967fa.accept_19_11_8_12_1_6204 30 65 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 65 126 (Polychromatic418967fa.accept_10_9_5_6_1_691 29 65 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 126 (accept_3_4 28 65 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 65 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 65 126
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 26 65 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 65 126 (accept_3_4 25 65 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  65 126 (Polychromatic418967fa.accept_10_4_5_6_1_651 24 65 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 65 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 65 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 126 (accept_3_4 22 65 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 65 126 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 65 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 65 126
  (Polychromatic418967fa.accept_16_4_1_14_1_3908 20 65 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 65 126 (accept_3_4 19 65 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  65 126 (Polychromatic418967fa.accept_15_3_5_6_1_4005 18 65 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 65 126 (Polychromatic418967fa.accept_11_6_10_5_1_341 17 65 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 126 (accept_3_4 16 65 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 65 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 65 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 65 126
  (Polychromatic418967fa.accept_10_4_5_6_1_651 14 65 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 65 126 (accept_3_4 13 65 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  65 126 (Polychromatic418967fa.accept_15_12_5_6_1_2148 12 65 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 65 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 65 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 65 126 (accept_3_4 10 65 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 65 126 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 65 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 126
  (Polychromatic418967fa.accept_17_8_14_7_1_6203 8 65 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 65 126 (accept_3_4 7 65 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65
  126 (Polychromatic418967fa.accept_11_6_10_5_1_341 6 65 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 65 126 (Polychromatic418967fa.accept_19_5_8_12_1_6093 5 65 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 65 126 (accept_3_4 4 65 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 65 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 65 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 126
  (Polychromatic418967fa.accept_25_2_15_1_1_6202 2 65 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 65 126 (accept_3_4 1 65 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65
  126)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 64 126 (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 64 126 2 31 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 64 126 (Polychromatic418967fa.accept_19_4_7_12_1_6201 61 64 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 64 126 2 30 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 64 126 (accept_3_5 59 64 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 64 126 2 29 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 64 126 (Polychromatic418967fa.accept_12_9_4_6_1_460 57 64 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 64 126 2 28 32 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 64 126
  (Polychromatic418967fa.accept_10_5_4_6_1_319 55 64 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 64 126 2 27 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 64 126 (accept_3_5 53 64 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 64
  126 2 26 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  64 126 (Polychromatic418967fa.accept_11_7_9_5_1_338 51 64 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 64 126 2 25 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 64 126 (Polychromatic418967fa.accept_13_10_12_9_1_1837 49 64 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 64 126 2 24 32 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 64 126 (accept_3_5 47 64 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 64 126 2 23 32 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 64 126
  (Polychromatic418967fa.accept_10_5_4_6_1_319 45 64 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 64 126 2 22 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 64 126 (Polychromatic418967fa.accept_15_13_4_6_1_3046 43 64 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 64 126 2 21 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 64 126 (accept_3_5 41 64 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 64 126 2 20 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 64 126 (Polychromatic418967fa.accept_12_3_4_6_1_434 39 64 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 64 126 2 19 32 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 64 126
  (Polychromatic418967fa.accept_19_18_7_12_1_6148 37 64 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 64 126 2 18 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 64 126 (accept_3_5 35 64 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 64
  126 2 17 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  64 126 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 64 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 64 126 2 16 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 64 126 (Polychromatic418967fa.accept_27_4_10_18_1_6200 31 64 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 64 126 2 15 32 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 64 126 (accept_3_5 29 64 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 64 126 2 14 32 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 64 126
  (Polychromatic418967fa.accept_12_3_4_6_1_434 27 64 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 64 126 2 13 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 64 126 (Polychromatic418967fa.accept_10_5_4_6_1_319 25 64 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 64 126 2 12 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 64 126 (accept_3_5 23 64 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 64 126 2 11 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 64 126 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 64 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 64 126 2 10 32 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 64 126
  (Polychromatic418967fa.accept_17_2_13_7_1_5011 19 64 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 64 126 2 9 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 64 126 (accept_3_5 17 64 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 64
  126 2 8 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  64 126 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 64 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 64 126 2 7 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 64 126 (Polychromatic418967fa.accept_15_13_4_6_1_3046 13 64 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 64 126 2 6 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 64 126 (accept_3_5 11 64 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64 126 2 5 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 64 126 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 64 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 64 126 2 4 32 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 64 126
  (Polychromatic418967fa.accept_11_7_9_5_1_338 7 64 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 64 126 2 3 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 64 126 (accept_3_5 5 64 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 64 126
  2 2 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 64
  126 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 64 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 64 126 2 1 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 64 126 (Polychromatic418967fa.accept_19_1_7_12_1_3443 1 64 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 64 126)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 63 126 (allA_succ_of_accept 62 63 126 (Polychromatic418967fa.accept_12_2_3_6_1_112 62 63 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 63 126
  (Polychromatic418967fa.accept_4_1_3_2_1_3 61 63 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 63 126 3 20 21 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 63 126 (Polychromatic418967fa.accept_10_9_3_6_1_686 59 63 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 126 (Polychromatic418967fa.accept_10_8_3_6_1_685 58 63 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 63 126 3 19 21 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 63 126 7 8 9 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 63 126
  (Polychromatic418967fa.accept_15_10_3_6_1_3042 55 63 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 63 126 9 6 7 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 63 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 63 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 126 (Polychromatic418967fa.accept_12_4_3_6_1_879 52 63 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 63 126 3 17 21 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 63 126
  (Polychromatic418967fa.accept_12_2_3_6_1_112 50 63 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 49 63 126 7 7 9 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 48 63 126 3 16 21 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 63 126 (Polychromatic418967fa.accept_10_7_3_6_1_644 47 63 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 126 (Polychromatic418967fa.accept_11_2_8_5_1_1219 46 63 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 63 126 9 5 7 14 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 63 126
  (Polychromatic418967fa.accept_12_8_3_6_1_909 44 63 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 126 (Polychromatic418967fa.accept_22_21_19_16_1_6199 43 63 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 63 126 21 2 3 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 63 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 63 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 126
  (Polychromatic418967fa.accept_12_4_3_6_1_879 40 63 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 63 126 3 13 21 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 63 126 (Polychromatic418967fa.accept_10_8_3_6_1_685 38 63 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 63 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 63 126 9 4 7 14 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 63 126 7 5 9 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 63 126
  (Polychromatic418967fa.accept_12_10_3_6_1_882 34 63 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 63 126 3 11 21 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 63 126 (Polychromatic418967fa.accept_12_8_3_6_1_909 32 63 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 126 (Polychromatic418967fa.accept_15_1_3_6_1_621 31 63 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 63 126 3 10 21 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 63 126
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 63 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 63 126 7 4 9 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 63 126 9 3 7 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 63 126 (Polychromatic418967fa.accept_12_2_3_6_1_112 26 63 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 63 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 63 126 3 8 21 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 63 126
  (Polychromatic418967fa.accept_16_7_15_14_1_2889 23 63 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 63 126 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 63 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63 126 21 1 3 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 63 126 (Polychromatic418967fa.accept_12_8_3_6_1_909 20 63 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 126
  (Polychromatic418967fa.accept_10_9_3_6_1_686 19 63 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 63 126 9 2 7 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 63 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 63 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 126 (Polychromatic418967fa.accept_12_4_3_6_1_879 16 63 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 63 126 3 5 21 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 63 126 7 2 9 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 63 126
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 63 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 63 126 3 4 21 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 63 126 (Polychromatic418967fa.accept_15_11_3_6_1_1306 11 63 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 126 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 63 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 63 126 9 1 7 14 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 63 126
  (Polychromatic418967fa.accept_10_8_3_6_1_685 8 63 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 63 126 7 1 9 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 63 126 3 2 21 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 63 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 63 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 126 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 63 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 63 126 3 1 21 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 63 126
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 2 63 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 63 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 63 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 63 126)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 62 126 (allA_succ_of_accept 61 62 126 (accept_3_4 61 62 126 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 62 126 2 30 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 62 126 (Polychromatic418967fa.accept_25_9_12_1_1_6198 59 62 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 62 126 2 29 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 62 126 (Polychromatic418967fa.accept_12_9_2_6_1_455 57
  62 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 62 126 2 28 31 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 62 126 (accept_3_4 55
  62 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 62 126 2 27 31 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 62 126
  (Polychromatic418967fa.accept_11_9_7_5_1_749 53 62 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 62 126 2 26 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 62 126 (Polychromatic418967fa.accept_10_1_2_6_1_638 51 62 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 62 126 2 25 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 62 126 (accept_3_4 49 62 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 62 126 2 24 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 62 126 (Polychromatic418967fa.accept_17_13_11_7_1_4961 47 62
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 62 126 2 23 31 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 62 126
  (Polychromatic418967fa.accept_12_9_2_6_1_455 45 62 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 62 126 2 22 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 62 126 (accept_3_4 43 62 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 62
  126 2 21 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  62 126 (Polychromatic418967fa.accept_10_1_2_6_1_638 41 62 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 62 126 2 20 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 62 126 (Polychromatic418967fa.accept_12_3_2_6_1_138 39 62 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 62 126 2 19 31 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 62 126 (accept_3_4 37 62 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 62 126 2 18 31 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 62 126
  (Polychromatic418967fa.accept_17_1_11_7_1_4962 35 62 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 62 126 2 17 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 62 126 (Polychromatic418967fa.accept_12_9_2_6_1_455 33 62 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 62 126 2 16 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 62 126 (accept_3_4 31 62 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 62 126 2 15 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 62 126 (Polychromatic418967fa.accept_23_6_16_11_1_6197 29 62
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 62 126 2 14 31 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 62 126
  (Polychromatic418967fa.accept_12_3_2_6_1_138 27 62 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 62 126 2 13 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 62 126 (accept_3_4 25 62 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 62
  126 2 12 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  62 126 (Polychromatic418967fa.accept_15_8_2_6_1_2125 23 62 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 62 126 2 11 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 62 126 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 62 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 62 126 2 10 31 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 62 126 (accept_3_4 19 62 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 62 126 2 9 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 62 126 (Polychromatic418967fa.accept_19_17_5_12_1_4753
  17 62 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 126 2 8 31 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 126
  (Polychromatic418967fa.accept_12_3_2_6_1_138 15 62 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 62 126 2 7 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 62 126 (accept_3_4 13 62 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62
  126 2 6 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  62 126 (Polychromatic418967fa.accept_10_1_2_6_1_638 11 62 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 62 126 2 5 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 62 126 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 62 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 126 2 4 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 126 (accept_3_4 7 62 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 62 126 2 3 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 62 126 (Polychromatic418967fa.accept_17_5_11_7_1_6146 5 62 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 126 2 2 31 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 126
  (Polychromatic418967fa.accept_12_3_2_6_1_138 3 62 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 62 126 2 1 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 62 126 (accept_3_4 1 62 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  126)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 126 (allA_succ_of_accept 60 61 126
  (Polychromatic418967fa.accept_24_12_13_6_1_6095 60 61 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 126 (accept_3_5 59 61 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 126 (Polychromatic418967fa.accept_16_10_13_14_1_5042 58 61 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 126 (Polychromatic418967fa.accept_10_7_1_6_1_673 57 61 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 126 (accept_3_5 56 61 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 61 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 126
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 54 61 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 126 (accept_3_5 53 61 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 126 (Polychromatic418967fa.accept_10_2_1_6_1_634 52 61 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 61 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 126 (accept_3_5 50 61 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 126 (Polychromatic418967fa.accept_16_1_13_14_1_1064 49 61 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 126
  (Polychromatic418967fa.accept_15_3_1_6_1_206 48 61 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 126 (accept_3_5 47 61 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 126 (Polychromatic418967fa.accept_19_8_4_12_1_4768 46 61 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 126 (Polychromatic418967fa.accept_10_5_1_6_1_672 45 61 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 126 (accept_3_5 44 61 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 61 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 126
  (Polychromatic418967fa.accept_10_2_1_6_1_634 42 61 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 126 (accept_3_5 41 61 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 126 (Polychromatic418967fa.accept_15_10_1_6_1_3033 40 61 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 61 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 126 (accept_3_5 38 61 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 126 (Polychromatic418967fa.accept_10_7_1_6_1_673 37 61 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 126
  (Polychromatic418967fa.accept_20_16_1_6_1_6196 36 61 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 126 (accept_3_5 35 61 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 126 (Polychromatic418967fa.accept_11_1_6_5_1_1732 34 61 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 126 (Polychromatic418967fa.accept_15_3_1_6_1_206 33 61 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 126 (accept_3_5 32 61 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 61 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 126
  (Polychromatic418967fa.accept_19_11_4_12_1_6106 30 61 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 126 (accept_3_5 29 61 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 126 (Polychromatic418967fa.accept_25_3_11_1_1_6195 28 61 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 61 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 126 (accept_3_5 26 61 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 126 (Polychromatic418967fa.accept_10_5_1_6_1_672 25 61 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 126
  (Polychromatic418967fa.accept_15_9_1_6_1_657 24 61 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 126 (accept_3_5 23 61 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 126 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 61 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 126 (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 61 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 126 (accept_3_5 20 61 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 61 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 126
  (Polychromatic418967fa.accept_15_3_1_6_1_206 18 61 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 126 (accept_3_5 17 61 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 126 (Polychromatic418967fa.accept_17_16_10_7_1_2671 16 61 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 61 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 126 (accept_3_5 14 61 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 126 (Polychromatic418967fa.accept_23_13_15_11_1_6194 13 61 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 126
  (Polychromatic418967fa.accept_10_2_1_6_1_634 12 61 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 126 (accept_3_5 11 61 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 126 (Polychromatic418967fa.accept_11_10_6_5_1_1239 10 61 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 126 (Polychromatic418967fa.accept_15_9_1_6_1_657 9 61 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 126 (accept_3_5 8 61 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 61 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 126
  (Polychromatic418967fa.accept_19_6_4_12_1_6193 6 61 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 126 (accept_3_5 5 61 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  126 (Polychromatic418967fa.accept_23_4_15_11_1_6192 4 61 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 61 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 61 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 126 (accept_3_5 2 61 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 61 126 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1 61 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61
  126))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 60 126 (allA_succ_of_accept 59 60 126
  (Polychromatic418967fa.accept_13_7_8_9_1_1158 59 60 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 60 126 2 29 30 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 57 60 126 3 19 20 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 56 60 126 2 28 30 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 60 126 (Polychromatic418967fa.accept_13_3_8_9_1_1134 55 60 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 126 6 9 10 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 126 (Polychromatic418967fa.accept_13_1_8_9_1_1154 53 60 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 126 2 26 30 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 60 126 3 17 20 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 60 126 2 25 30 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 60 126
  (Polychromatic418967fa.accept_17_15_9_7_1_3816 49 60 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 60 126 6 8 10 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 60 126 (Polychromatic418967fa.accept_19_9_3_12_1_6191 47 60 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60 126 2 23 30 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 60 126 3 15 20 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 60 126 2 22 30 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 126 (Polychromatic418967fa.accept_13_4_8_9_1_1156
  43 60 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 126 6 7 10 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 126
  (Polychromatic418967fa.accept_24_17_12_6_1_6190 41 60 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 60 126 2 20 30 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 60 126 3 13 20 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 38 60 126 2 19 30 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 60 126 (Polychromatic418967fa.accept_13_11_8_9_1_1161 37 60 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 126 6 6 10 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 126 (Polychromatic418967fa.accept_23_12_14_11_1_6189 35 60
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 126 2 17 30 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 60 126 3 11 20 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 60 126 2 16 30 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 60 126
  (Polychromatic418967fa.accept_24_7_12_6_1_6188 31 60 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 60 126 6 5 10 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 60 126 (Polychromatic418967fa.accept_13_3_8_9_1_1134 29 60 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60 126 2 14 30 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 60 126 3 9 20 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 60 126 2 13 30 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 60 126 (Polychromatic418967fa.accept_13_12_8_9_1_1833
  25 60 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 126 6 4 10 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 126
  (Polychromatic418967fa.accept_24_23_12_6_1_6187 23 60 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 60 126 2 11 30 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 60 126 3 7 20 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 60 126 2 10 30 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 60 126 (Polychromatic418967fa.accept_17_2_9_7_1_5002 19 60 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 126 6 3 10 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 126 (Polychromatic418967fa.accept_13_4_8_9_1_1156 17 60 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60 126 2 8 30 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 60 126 3 5 20 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 60 126 2 7 30 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 126
  (Polychromatic418967fa.accept_19_13_3_12_1_6186 13 60 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 60 126 6 2 10 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 60 126 (Polychromatic418967fa.accept_13_11_8_9_1_1161 11 60 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 126 2 5 30 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 60 126 3 3 20 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 60 126 2 4 30 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 126 (Polychromatic418967fa.accept_13_7_8_9_1_1158 7 60 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 126 6 1 10 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 126
  (Polychromatic418967fa.accept_17_5_9_7_1_6185 5 60 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 60 126 2 2 30 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 60 126 3 1 20 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 60 126 2 1 30 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 60 126 (Polychromatic418967fa.accept_13_1_8_9_1_1154 1 60 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 60 126))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 59 126 (allA_succ_of_accept 58 59 126 (accept_3_4 58 59 126 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 59 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 59 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 59 126 (Polychromatic418967fa.accept_13_4_7_9_1_5260 56 59 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 126 (accept_3_4 55 59 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 126 (Polychromatic418967fa.accept_11_10_4_5_1_359
  54 59 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 126
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 59 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 126 (accept_3_4 52 59 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 126 (Polychromatic418967fa.accept_16_3_11_14_1_446 51 59 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 126 (Polychromatic418967fa.accept_13_11_7_9_1_612 50 59 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 126 (accept_3_4 49 59 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 126 (Polychromatic418967fa.accept_17_14_8_7_1_6183 48 59 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 126
  (Polychromatic418967fa.accept_13_8_7_9_1_611 47 59 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 126 (accept_3_4 46 59 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 59 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 126 (Polychromatic418967fa.accept_19_6_2_12_1_6136 44 59 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 126 (accept_3_4 43 59 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 126 (Polychromatic418967fa.accept_13_3_7_9_1_1153 42 59 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 126
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 59 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 126 (accept_3_4 40 59 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 126 (Polychromatic418967fa.accept_15_9_14_6_1_3004 39 59 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 126 (Polychromatic418967fa.accept_15_8_14_6_1_3003 38 59 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 126 (accept_3_4 37 59 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 126 (Polychromatic418967fa.accept_19_17_2_12_1_4751 36 59
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 126
  (Polychromatic418967fa.accept_10_5_9_6_1_697 35 59 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 126 (accept_3_4 34 59 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 59 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 126 (Polychromatic418967fa.accept_11_10_4_5_1_359 32 59 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 126 (accept_3_4 31 59 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 126 (Polychromatic418967fa.accept_13_4_7_9_1_5260 30 59 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 126
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 59 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 126 (accept_3_4 28 59 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 126 (Polychromatic418967fa.accept_20_7_19_6_1_4742 27 59 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 126 (Polychromatic418967fa.accept_22_4_15_16_1_6184 26 59 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 126 (accept_3_4 25 59 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 126 (Polychromatic418967fa.accept_13_11_7_9_1_612 24 59 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 126
  (Polychromatic418967fa.accept_10_3_9_6_1_94 23 59 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 126 (accept_3_4 22 59 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 59 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 126 (Polychromatic418967fa.accept_15_5_14_6_1_5120 20 59 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 126 (accept_3_4 19 59 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 126 (Polychromatic418967fa.accept_17_1_8_7_1_4982 18 59 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 126
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 59 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 126 (accept_3_4 16 59 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 126 (Polychromatic418967fa.accept_10_5_9_6_1_697 15 59 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 126 (Polychromatic418967fa.accept_17_14_8_7_1_6183 14 59 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 126 (accept_3_4 13 59 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 126 (Polychromatic418967fa.accept_24_12_11_6_1_6182 12 59
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 126
  (Polychromatic418967fa.accept_13_11_7_9_1_612 11 59 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 126 (accept_3_4 10 59 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 59 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 59 126 (Polychromatic418967fa.accept_13_8_7_9_1_611 8 59 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 126 (accept_3_4 7 59 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 59 126 (Polychromatic418967fa.accept_13_6_7_9_1_1848 6 59 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 59
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 126 (accept_3_4 4 59 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59 126 (Polychromatic418967fa.accept_10_3_9_6_1_94 3
  59 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 126
  (Polychromatic418967fa.accept_13_2_7_9_1_2616 2 59 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 59 126 (accept_3_4 1 59 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59
  126))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 126 (allA_succ_of_accept 57 58 126
  (Polychromatic418967fa.accept_12_9_10_6_1_872 57 58 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 58 126 2 28 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 58 126 (Polychromatic418967fa.accept_13_3_6_9_1_1150 55 58 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 58 126 2 27 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 58 126 (accept_3_5 53 58 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 58 126 2 26 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 58 126 (Polychromatic418967fa.accept_12_3_10_6_1_442 51 58 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 58 126 2 25 29 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 58 126
  (Polychromatic418967fa.accept_13_10_6_9_1_1152 49 58 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 58 126 2 24 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 58 126 (accept_3_5 47 58 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 58
  126 2 23 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  58 126 (Polychromatic418967fa.accept_12_9_10_6_1_872 45 58 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 58 126 2 22 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 58 126 (Polychromatic418967fa.accept_10_3_8_6_1_326 43 58 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 58 126 2 21 29 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 58 126 (accept_3_5 41 58 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 58 126 2 20 29 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 58 126
  (Polychromatic418967fa.accept_12_3_10_6_1_442 39 58 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 58 126 2 19 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 58 126 (Polychromatic418967fa.accept_15_7_13_6_1_696 37 58 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 58 126 2 18 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 58 126 (accept_3_5 35 58 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 58 126 2 17 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 58 126 (Polychromatic418967fa.accept_10_3_8_6_1_326 33 58 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 58 126 2 16 29 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 58 126
  (Polychromatic418967fa.accept_16_15_10_14_1_2872 31 58 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 58 126 2 15 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 58 126 (accept_3_5 29 58 126 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 58 126 2 14 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 58 126 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 58 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 58 126 2 13 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 58 126 (Polychromatic418967fa.accept_22_3_14_16_1_6181
  25 58 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 58 126 2 12 29 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 58 126 (accept_3_5 23
  58 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 58 126 2 11 29 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 58 126
  (Polychromatic418967fa.accept_12_9_10_6_1_872 21 58 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 58 126 2 10 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 58 126 (Polychromatic418967fa.accept_11_8_3_5_1_355 19 58 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 58 126 2 9 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 58 126 (accept_3_5 17 58 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 58 126 2 8 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 58 126 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 58 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 58 126 2 7 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 58 126 (Polychromatic418967fa.accept_10_3_8_6_1_326 13
  58 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 58 126 2 6 29 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 58 126 (accept_3_5 11
  58 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58 126 2 5 29 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 58 126
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 58 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 58 126 2 4 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 58 126 (Polychromatic418967fa.accept_13_7_6_9_1_1831 7 58 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 126 2 3 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 126 (accept_3_5 5 58 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 58 126 2 2 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 58 126 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 58 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 58 126 2 1 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 58 126 (Polychromatic418967fa.accept_13_1_6_9_1_1197 1
  58 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  126)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 126 (allA_succ_of_accept 56 57 126
  (Polychromatic418967fa.accept_12_8_9_6_1_127 56 57 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 57 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 57 126 3 18 19 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 57 126 (Polychromatic418967fa.accept_10_3_7_6_1_659 53
  57 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 126
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 52 57 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 57 126 3 17 19 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 57 126 (Polychromatic418967fa.accept_12_2_9_6_1_439 50 57 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 126 (Polychromatic418967fa.accept_20_9_17_6_1_6098 49 57
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 57 126 3 16 19 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 57 126
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 57 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 57 126 (Polychromatic418967fa.accept_12_10_9_6_1_1445 46 57 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 57 126 3 15 19 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 57 126 (Polychromatic418967fa.accept_12_8_9_6_1_127 44
  57 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 126
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 57 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 57 126 3 14 19 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 57 126 (Polychromatic418967fa.accept_10_1_7_6_1_91 41 57 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 126 (Polychromatic418967fa.accept_12_4_9_6_1_440 40 57 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 57 126 3 13 19 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 57 126
  (Polychromatic418967fa.accept_12_2_9_6_1_439 38 57 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 126 (Polychromatic418967fa.accept_15_7_12_6_1_1327 37 57 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 57 126 3 12 19 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 57 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 35
  57 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 126
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 34 57 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 57 126 3 11 19 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 57 126 (Polychromatic418967fa.accept_12_8_9_6_1_127 32 57 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 57 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 57 126 3 10 19 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 57 126
  (Polychromatic418967fa.accept_13_3_5_9_1_5285 29 57 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 57 126 (Polychromatic418967fa.accept_12_4_9_6_1_440 28 57 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 57 126 3 9 19 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 57 126 (Polychromatic418967fa.accept_12_2_9_6_1_439 26 57 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 126
  (Polychromatic418967fa.accept_15_10_12_6_1_3000 25 57 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 57 126 3 8 19 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 57 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 57 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 126 (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 57
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 57 126 3 7 19 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 57 126
  (Polychromatic418967fa.accept_12_8_9_6_1_127 20 57 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 57 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 57 126 3 6 19 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 57 126 (Polychromatic418967fa.accept_13_4_5_9_1_1829 17 57 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 126
  (Polychromatic418967fa.accept_12_4_9_6_1_440 16 57 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 57 126 3 5 19 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 57 126 (Polychromatic418967fa.accept_12_2_9_6_1_439 14 57 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 126 (Polychromatic418967fa.accept_10_3_7_6_1_659 13 57 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 57 126 3 4 19 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 57 126
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 57 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 57 126 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 57 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 57 126 3 3 19 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 57 126 (Polychromatic418967fa.accept_11_8_2_5_1_1769 8 57 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 126
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 57 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 57 126 3 2 19 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 57 126 (Polychromatic418967fa.accept_15_5_12_6_1_639 5 57 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 126 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 57 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 57 126 3 1 19 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 57 126
  (Polychromatic418967fa.accept_12_2_9_6_1_439 2 57 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 57 126 (Polychromatic418967fa.accept_10_1_7_6_1_91 1 57 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 57 126))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  56 126 (allA_succ_of_accept 55 56 126 (accept_3_4 55 56 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  54 56 126 2 27 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 56 126 (Polychromatic418967fa.accept_19_15_18_12_1_6180 53 56 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 56 126 2 26 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 56 126 (Polychromatic418967fa.accept_12_3_8_6_1_895 51
  56 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 56 126 2 25 28 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 49 56 126 7 7 8 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 56 126 2 24 28 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 56 126
  (Polychromatic418967fa.accept_13_8_4_9_1_1145 47 56 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 56 126 2 23 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 56 126 (Polychromatic418967fa.accept_12_9_8_6_1_466 45 56 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 56 126 2 22 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 56 126 (accept_3_4 43 56 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56 126 14 3 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 56 126 (Polychromatic418967fa.accept_20_1_16_6_1_4715 41 56 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 56 126 2 20 28 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 56 126
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 39 56 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 56 126 2 19 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 56 126 (accept_3_4 37 56 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 56
  126 2 18 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 56
  126 7 5 8 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 56
  126 2 17 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  56 126 (Polychromatic418967fa.accept_12_9_8_6_1_466 33 56 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 56 126 2 16 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 56 126 (accept_3_4 31 56 126 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 56 126 2 15 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 56 126 (Polychromatic418967fa.accept_17_12_5_7_1_6179 29 56 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 56 126 14 2 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 56 126 (Polychromatic418967fa.accept_12_3_8_6_1_895 27 56 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 56 126 2 13 28 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 56 126 (accept_3_4 25
  56 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 56 126 2 12 28 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 56 126
  (Polychromatic418967fa.accept_22_1_12_16_1_6178 23 56 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 56 126 2 11 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 56 126 7 3 8 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 56 126 2 10 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 56 126 (accept_3_4 19 56 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56
  126 2 9 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  56 126 (Polychromatic418967fa.accept_11_6_1_5_1_2388 17 56 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 56 126 2 8 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 56 126 (Polychromatic418967fa.accept_12_3_8_6_1_895 15 56 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 126 14 1 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 126 (accept_3_4 13 56 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56 126 2 6 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 56 126 (Polychromatic418967fa.accept_17_11_5_7_1_6177 11 56 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 56 126 2 5 28 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 56 126
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 56 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 56 126 2 4 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 56 126 7 1 8 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 56 126 2 3 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 56 126 (Polychromatic418967fa.accept_13_5_4_9_1_601 5 56 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 56 126 2 2 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 56 126 (Polychromatic418967fa.accept_12_3_8_6_1_895 3 56 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 56 126 2 1 28 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 56 126 (accept_3_4 1 56 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 126))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 126 (allA_succ_of_accept 54 55 126 (Polychromatic418967fa.accept_10_4_5_6_1_651 54 55 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 126 (accept_3_5 53 55 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 55 126 (Polychromatic418967fa.accept_16_4_7_14_1_3897 52 55
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 126
  (Polychromatic418967fa.accept_10_1_5_6_1_649 51 55 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 55 126 (accept_3_5 50 55 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  55 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 55 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 55 126 (Polychromatic418967fa.accept_15_3_10_6_1_632 48 55 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 126 (accept_3_5 47 55 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 55 126 (Polychromatic418967fa.accept_13_7_3_9_1_1142 46 55 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 55 126
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 55 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 55 126 (accept_3_5 44 55 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  55 126 (Polychromatic418967fa.accept_19_5_17_12_1_6120 43 55 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 55 126 (Polychromatic418967fa.accept_15_12_10_6_1_2134 42 55 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 55 126 (accept_3_5 41 55 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 55 126 (Polychromatic418967fa.accept_19_2_17_12_1_6097 40 55
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 55 126
  (Polychromatic418967fa.accept_10_9_5_6_1_691 39 55 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 55 126 (accept_3_5 38 55 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  55 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 55 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 55 126 (Polychromatic418967fa.accept_16_4_7_14_1_3897 36 55 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 55 126 (accept_3_5 35 55 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 55 126 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 55 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 55 126
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 55 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 55 126 (accept_3_5 32 55 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  55 126 (Polychromatic418967fa.accept_10_1_5_6_1_649 31 55 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 55 126 (Polychromatic418967fa.accept_20_10_15_6_1_2149 30 55 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 55 126 (accept_3_5 29 55 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 126 (Polychromatic418967fa.accept_13_2_3_9_1_2610 28 55 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 126
  (Polychromatic418967fa.accept_15_12_10_6_1_2134 27 55 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 126 (accept_3_5 26 55 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  55 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 55 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 55 126 (Polychromatic418967fa.accept_10_4_5_6_1_651 24 55 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 126 (accept_3_5 23 55 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 55 126 (Polychromatic418967fa.accept_19_3_17_12_1_6176 22 55 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 126
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 55 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 55 126 (accept_3_5 20 55 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  55 126 (Polychromatic418967fa.accept_10_9_5_6_1_691 19 55 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 55 126 (Polychromatic418967fa.accept_13_5_3_9_1_1189 18 55 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 126 (accept_3_5 17 55 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 126 (Polychromatic418967fa.accept_15_1_10_6_1_631 16 55 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 55 126
  (Polychromatic418967fa.accept_13_2_3_9_1_2610 15 55 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 55 126 (accept_3_5 14 55 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  55 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 55 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 55 126 (Polychromatic418967fa.accept_13_12_3_9_1_4341 12 55 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 126 (accept_3_5 11 55 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 55 126 (Polychromatic418967fa.accept_16_10_7_14_1_2882 10 55
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 126
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 55 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 55 126 (accept_3_5 8 55 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55
  126 (Polychromatic418967fa.accept_13_7_3_9_1_1142 7 55 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 55 126 (Polychromatic418967fa.accept_13_6_3_9_1_1827 6 55 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 55 126 (accept_3_5 5 55 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 55 126 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 55 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 126
  (Polychromatic418967fa.accept_15_3_10_6_1_632 3 55 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 55 126 (accept_3_5 2 55 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55
  126 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 55 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 55 126))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 126 (allA_succ_of_accept 53 54
  126 (Polychromatic418967fa.accept_13_1_2_9_1_1186 53 54 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 54 126 2 26 27 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 51 54 126 3 17 18 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 50 54 126 2 25 27 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 54 126 (Polychromatic418967fa.accept_15_4_9_6_1_627 49 54 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 126 6 8 9 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 126
  (Polychromatic418967fa.accept_19_9_16_12_1_4760 47 54 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 54 126 2 23 27 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 54 126 9 5 6 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 44 54 126 2 22 27 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 54 126 (Polychromatic418967fa.accept_19_5_16_12_1_6175 43 54 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 126 6 7 9 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 126 (Polychromatic418967fa.accept_15_11_9_6_1_1321 41 54 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 54 126 2 20 27 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 54 126 3 13 18 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 54 126 2 19 27 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 54 126
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 37 54 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 54 126 18 2 3 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 54 126 (Polychromatic418967fa.accept_10_5_4_6_1_319 35 54 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 54 126 2 17 27 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 54 126 3 11 18 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 54 126 2 16 27 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 126 (Polychromatic418967fa.accept_13_5_2_9_1_1195
  31 54 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 126 6 5 9 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 126
  (Polychromatic418967fa.accept_13_3_2_9_1_1187 29 54 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 54 126 2 14 27 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 54 126 9 3 6 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 54 126 2 13 27 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 54 126 (Polychromatic418967fa.accept_10_5_4_6_1_319 25 54 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 126 6 4 9 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 126 (Polychromatic418967fa.accept_19_4_16_12_1_485 23 54 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54 126 2 11 27 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 54 126 3 7 18 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 54 126 2 10 27 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 126
  (Polychromatic418967fa.accept_13_6_2_9_1_1188 19 54 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 54 126 18 1 3 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 54 126 (Polychromatic418967fa.accept_11_6_10_5_1_341 17 54 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 126 2 8 27 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 54 126 3 5 18 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 54 126 2 7 27 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 126 (Polychromatic418967fa.accept_19_13_16_12_1_6096 13 54
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 126 6 2 9 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 126
  (Polychromatic418967fa.accept_13_11_2_9_1_2640 11 54 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 54 126 2 5 27 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 54 126 9 1 6 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 54 126 2 4 27 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 54 126 (Polychromatic418967fa.accept_13_7_2_9_1_1826 7 54 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 126 6 1 9 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 126 (Polychromatic418967fa.accept_10_5_4_6_1_319 5 54 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 126 2 2 27 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 54 126 3 1 18 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 54 126 2 1 27 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 126
  (Polychromatic418967fa.accept_13_1_2_9_1_1186 1 54 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 54 126)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 126 (allA_succ_of_accept 52 53
  126 (accept_3_4 52 53 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 126
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 53 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 126 (Polychromatic418967fa.accept_13_11_1_9_1_1179 50 53 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 126 (accept_3_4 49 53 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 126 (Polychromatic418967fa.accept_10_8_3_6_1_685 48 53 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 47
  53 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 126 (accept_3_4 46 53
  126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 126
  (Polychromatic418967fa.accept_13_6_1_9_1_619 45 53 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 53 126 (Polychromatic418967fa.accept_13_5_1_9_1_618 44 53 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 126 (accept_3_4 43 53 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 53 126 (Polychromatic418967fa.accept_16_10_5_14_1_6173 42 53 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 126
  (Polychromatic418967fa.accept_13_2_1_9_1_1174 41 53 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 126 (accept_3_4 40 53 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 53 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 126 (Polychromatic418967fa.accept_10_8_3_6_1_685 38 53 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 126 (accept_3_4 37 53 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 126 (Polychromatic418967fa.accept_13_10_1_9_1_3380 36 53 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 126
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 53 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 126 (accept_3_4 34 53 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 126 (Polychromatic418967fa.accept_22_11_9_16_1_6174 33 53 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 126 (Polychromatic418967fa.accept_13_6_1_9_1_619 32 53 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 126 (accept_3_4 31 53 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 126 (Polychromatic418967fa.accept_17_13_2_7_1_6122 30 53 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 126
  (Polychromatic418967fa.accept_10_9_3_6_1_686 29 53 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 126 (accept_3_4 28 53 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 53 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 126 (Polychromatic418967fa.accept_16_10_5_14_1_6173 26 53 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 126 (accept_3_4 25 53 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 126 (Polychromatic418967fa.accept_13_11_1_9_1_1179 24 53
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 126
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 53 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 126 (accept_3_4 22 53 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 126 (Polychromatic418967fa.accept_13_8_1_9_1_1178 21 53 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 126 (Polychromatic418967fa.accept_25_20_3_1_1_6172 20 53 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 126 (accept_3_4 19 53 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 126 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 53 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 126
  (Polychromatic418967fa.accept_10_7_3_6_1_644 17 53 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 126 (accept_3_4 16 53 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 53 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 126 (Polychromatic418967fa.accept_15_14_8_6_1_2133 14 53 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 126 (accept_3_4 13 53 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 126 (Polychromatic418967fa.accept_17_12_2_7_1_3813 12 53
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 126
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 53 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 126 (accept_3_4 10 53 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 126 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 53 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 126 (Polychromatic418967fa.accept_10_8_3_6_1_685 8 53 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 126 (accept_3_4 7 53 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 126 (Polychromatic418967fa.accept_13_6_1_9_1_619 6 53 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 126
  (Polychromatic418967fa.accept_13_5_1_9_1_618 5 53 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 126 (accept_3_4 4 53 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  126 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 53 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 126 (Polychromatic418967fa.accept_13_2_1_9_1_1174 2 53 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 126 (accept_3_4 1 53 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 126))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 126
  (allA_succ_of_accept 51 52 126 (Polychromatic418967fa.accept_10_1_2_6_1_638 51 52 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 52 126 2 25 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 52 126 (Polychromatic418967fa.accept_16_1_4_14_1_1896
  49 52 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 52 126 2 24 26 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 52 126 (accept_3_5 47
  52 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 52 126 2 23 26 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 52 126
  (Polychromatic418967fa.accept_12_9_4_6_1_460 45 52 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 52 126 2 22 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 52 126 (Polychromatic418967fa.accept_15_13_7_6_1_682 43 52 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 52 126 2 21 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 52 126 (accept_3_5 41 52 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 52 126 2 20 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 52 126 (Polychromatic418967fa.accept_12_3_4_6_1_434 39 52 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 52 126 2 19 26 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 52 126
  (Polychromatic418967fa.accept_20_17_12_6_1_6171 37 52 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 52 126 2 18 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 52 126 (accept_3_5 35 52 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 52
  126 2 17 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  52 126 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 52 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 52 126 2 16 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 52 126 (Polychromatic418967fa.accept_10_1_2_6_1_638 31 52 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 52 126 2 15 26 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 52 126 (accept_3_5 29 52 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 52 126 2 14 26 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 52 126
  (Polychromatic418967fa.accept_12_3_4_6_1_434 27 52 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 52 126 2 13 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 52 126 (Polychromatic418967fa.accept_11_3_8_5_1_336 25 52 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 52 126 2 12 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 52 126 (accept_3_5 23 52 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 52 126 2 11 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 52 126 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 52 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 52 126 2 10 26 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 52 126
  (Polychromatic418967fa.accept_22_19_8_16_1_3106 19 52 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 52 126 2 9 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 52 126 (accept_3_5 17 52 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52
  126 2 8 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  52 126 (Polychromatic418967fa.accept_12_3_4_6_1_434 15 52 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 52 126 2 7 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 52 126 (Polychromatic418967fa.accept_11_2_8_5_1_1219 13 52 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 52 126 2 6 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 52 126 (accept_3_5 11 52 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 52 126 2 5 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 52 126 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 52 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 52 126 2 4 26 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 52 126
  (Polychromatic418967fa.accept_16_7_4_14_1_2860 7 52 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 52 126 2 3 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 52 126 (accept_3_5 5 52 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 52 126
  2 2 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 52
  126 (Polychromatic418967fa.accept_11_3_8_5_1_336 3 52 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 52 126 2 1 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 52 126 (Polychromatic418967fa.accept_10_1_2_6_1_638 1 52 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 52 126)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 126
  (allA_succ_of_accept 50 51 126 (Polychromatic418967fa.accept_12_2_3_6_1_112 50 51 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 51 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 51 126 3 16 17 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 51 126
  (Polychromatic418967fa.accept_10_7_1_6_1_673 47 51 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 51 126 (Polychromatic418967fa.accept_12_10_3_6_1_882 46 51 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 51 126 3 15 17 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 51 126 (Polychromatic418967fa.accept_12_8_3_6_1_909 44
  51 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 126
  (Polychromatic418967fa.accept_16_11_3_14_1_5043 43 51 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 51 126 3 14 17 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 51 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 51 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 126 (Polychromatic418967fa.accept_12_4_3_6_1_879 40 51 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 51 126 3 13 17 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 51 126
  (Polychromatic418967fa.accept_12_2_3_6_1_112 38 51 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 51 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 51 126 3 12 17 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 51 126 (Polychromatic418967fa.accept_10_5_1_6_1_672 35
  51 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 126
  (Polychromatic418967fa.accept_12_10_3_6_1_882 34 51 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 51 126 3 11 17 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 51 126 (Polychromatic418967fa.accept_10_2_1_6_1_634 32 51 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 126 (Polychromatic418967fa.accept_11_9_7_5_1_749 31 51 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 51 126 3 10 17 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 51 126
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 51 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 51 126 (Polychromatic418967fa.accept_12_4_3_6_1_879 28 51 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 51 126 3 9 17 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 51 126 (Polychromatic418967fa.accept_12_2_3_6_1_112 26 51 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 126
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 51 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 51 126 3 8 17 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 51 126 (Polychromatic418967fa.accept_13_10_12_9_1_1837 23 51 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 126 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 51 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 51 126 3 7 17 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 51 126
  (Polychromatic418967fa.accept_11_9_7_5_1_749 20 51 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 126 (Polychromatic418967fa.accept_27_19_24_18_1_6170 19 51 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 51 126 3 6 17 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 51 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 51 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 126
  (Polychromatic418967fa.accept_12_4_3_6_1_879 16 51 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 51 126 3 5 17 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 51 126 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 51 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 51 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 51 126 3 4 17 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 51 126
  (Polychromatic418967fa.accept_16_11_3_14_1_5043 11 51 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 51 126 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 51 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 51 126 3 3 17 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 51 126 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 51 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 126
  (Polychromatic418967fa.accept_10_7_1_6_1_673 7 51 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 51 126 3 2 17 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 51 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 51 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 126 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 51 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 51 126 3 1 17 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 51 126
  (Polychromatic418967fa.accept_10_2_1_6_1_634 2 51 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 51 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 51 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 51 126))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 126
  (allA_succ_of_accept 49 50 126 (accept_3_4 49 50 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 50
  126 2 24 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  50 126 (Polychromatic418967fa.accept_13_8_11_9_1_593 47 50 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 50 126 2 23 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 50 126 (Polychromatic418967fa.accept_11_1_6_5_1_1732 45 50 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 50 126 2 22 25 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 50 126 (accept_3_4 43 50 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 50 126 2 21 25 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 50 126
  (Polychromatic418967fa.accept_13_2_11_9_1_591 41 50 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 50 126 2 20 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 50 126 (Polychromatic418967fa.accept_12_3_2_6_1_138 39 50 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 50 126 2 19 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 50 126 (accept_3_4 37 50 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 50 126 2 18 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 50 126 (Polychromatic418967fa.accept_20_15_10_6_1_6169 35 50
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 50 126 2 17 25 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 50 126
  (Polychromatic418967fa.accept_12_9_2_6_1_455 33 50 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 50 126 2 16 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 50 126 (accept_3_4 31 50 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50
  126 2 15 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  50 126 (Polychromatic418967fa.accept_15_14_5_6_1_6168 29 50 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 50 126 2 14 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 50 126 (Polychromatic418967fa.accept_12_3_2_6_1_138 27 50 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 50 126 2 13 25 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 50 126 (accept_3_4 25 50 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 50 126 2 12 25 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 50 126
  (Polychromatic418967fa.accept_11_1_6_5_1_1732 23 50 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 50 126 2 11 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 50 126 (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 50 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 126 2 10 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 126 (accept_3_4 19 50 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 50 126 2 9 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 50 126 (Polychromatic418967fa.accept_23_17_4_11_1_6167 17 50 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 50 126 2 8 25 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 50 126
  (Polychromatic418967fa.accept_12_3_2_6_1_138 15 50 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 50 126 2 7 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 50 126 (accept_3_4 13 50 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50
  126 2 6 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  50 126 (Polychromatic418967fa.accept_15_11_5_6_1_669 11 50 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 50 126 2 5 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 50 126 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 50 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 126 2 4 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 126 (accept_3_4 7 50 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 50 126 2 3 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 50 126 (Polychromatic418967fa.accept_20_5_10_6_1_6166 5 50 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 50 126 2 2 25 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 50 126
  (Polychromatic418967fa.accept_12_3_2_6_1_138 3 50 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 50 126 2 1 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 50 126 (accept_3_4 1 50 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50
  126)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 126 (allA_succ_of_accept 48 49 126
  (Polychromatic418967fa.accept_19_10_11_12_1_6114 48 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 49 126 (accept_3_5 47 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 49 126 (Polychromatic418967fa.accept_19_8_11_12_1_6165 46 49 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 126 (Polychromatic418967fa.accept_10_5_9_6_1_697 45 49 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 126 (accept_3_5 44 49 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 43
  49 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 49 126 7 6 7 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 49 126 (accept_3_5 41
  49 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 49 126
  (Polychromatic418967fa.accept_13_1_10_9_1_215 40 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 49 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 49 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 126 (accept_3_5 38 49 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 49 126 (Polychromatic418967fa.accept_19_18_11_12_1_6163 37 49 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 126
  (Polychromatic418967fa.accept_16_4_1_14_1_3908 36 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 49 126 7 5 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 49 126 (Polychromatic418967fa.accept_20_14_9_6_1_3346 34 49 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 126 (Polychromatic418967fa.accept_10_3_9_6_1_94 33 49 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 126 (accept_3_5 32 49 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 31
  49 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 126
  (Polychromatic418967fa.accept_20_10_9_6_1_6164 30 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 126 (accept_3_5 29 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 49
  126 7 4 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  49 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 49 126 (accept_3_5 26 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 49 126 (Polychromatic418967fa.accept_10_5_9_6_1_697 25 49 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 126 (Polychromatic418967fa.accept_15_9_4_6_1_3075 24 49 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 126 (accept_3_5 23 49 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 126 (Polychromatic418967fa.accept_17_5_15_7_1_4992
  22 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 49 126 7 3 7 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 49 126 (accept_3_5 20
  49 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 126
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 49 126 (Polychromatic418967fa.accept_19_18_11_12_1_6163 18 49 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 126 (accept_3_5 17 49 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 49 126 (Polychromatic418967fa.accept_24_16_1_6_1_6162 16 49 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 126
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 49 126 7 2 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 49 126 (Polychromatic418967fa.accept_10_3_9_6_1_94 13 49 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 126 (Polychromatic418967fa.accept_13_12_10_9_1_1166 12 49
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 126 (accept_3_5 11 49 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 126 (Polychromatic418967fa.accept_15_10_4_6_1_2129
  10 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 126
  (Polychromatic418967fa.accept_15_9_4_6_1_3075 9 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 126 (accept_3_5 8 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 49 126
  7 1 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 49 126
  (Polychromatic418967fa.accept_13_6_10_9_1_4329 6 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 126 (accept_3_5 5 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  126 (Polychromatic418967fa.accept_16_4_1_14_1_3908 4 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 49 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 49 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 126 (accept_3_5 2 49 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 126 (Polychromatic418967fa.accept_13_1_10_9_1_215 1 49 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 126)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 48 126 (allA_succ_of_accept 47 48 126 (Polychromatic418967fa.accept_19_9_10_12_1_6161 47 48 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 126 2 23 24 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 48 126 3 15 16 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 48 126 2 22 24 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 48 126
  (Polychromatic418967fa.accept_10_3_8_6_1_326 43 48 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 48 126 6 7 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 48 126 (Polychromatic418967fa.accept_15_11_3_6_1_1306 41 48 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 126 2 20 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 48 126 3 13 16 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 48 126 2 19 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 126 (Polychromatic418967fa.accept_22_15_4_16_1_6160
  37 48 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 126 6 6 8 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 126
  (Polychromatic418967fa.accept_15_5_3_6_1_2128 35 48 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 48 126 2 17 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 48 126 3 11 16 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 48 126 2 16 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 48 126 (Polychromatic418967fa.accept_15_1_3_6_1_621 31 48 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 126 6 5 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 126 (Polychromatic418967fa.accept_25_4_23_1_1_6159 29 48 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48 126 2 14 24 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 48 126 3 9 16 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 48 126 2 13 24 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 126
  (Polychromatic418967fa.accept_15_10_3_6_1_3042 25 48 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 48 126 6 4 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 48 126 (Polychromatic418967fa.accept_10_3_8_6_1_326 23 48 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 126 2 11 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 48 126 3 7 16 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 48 126 2 10 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 48 126 (Polychromatic418967fa.accept_22_19_4_16_1_6158
  19 48 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 126 6 3 8 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 126
  (Polychromatic418967fa.accept_19_17_10_12_1_6157 17 48 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 48 126 2 8 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 48 126 3 5 16 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 48 126 2 7 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 48 126 (Polychromatic418967fa.accept_10_3_8_6_1_326 13 48 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 126 6 2 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 126 (Polychromatic418967fa.accept_15_11_3_6_1_1306
  11 48 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 126 2 5 24 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 48 126 3 3 16 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 48 126 2 4 24 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 48 126
  (Polychromatic418967fa.accept_25_7_23_1_1_6156 7 48 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 48 126 6 1 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 48 126 (Polychromatic418967fa.accept_15_5_3_6_1_2128 5 48 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 126 2 2 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 48 126 3 1 16 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 48 126 2 1 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 126 (Polychromatic418967fa.accept_15_1_3_6_1_621 1 48 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48
  126)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 126 (allA_succ_of_accept 46 47 126 (accept_3_4 46 47
  126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 126 (Polychromatic418967fa.accept_4_1_3_2_1_3
  45 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 47 126
  (Polychromatic418967fa.accept_23_21_1_11_1_6155 44 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 47 126 (accept_3_4 43 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  47 126 (Polychromatic418967fa.accept_13_3_8_9_1_1134 42 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 47 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 47 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 126 (accept_3_4 40 47 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 126 (Polychromatic418967fa.accept_16_7_15_14_1_2889 39 47 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 47 126
  (Polychromatic418967fa.accept_13_12_8_9_1_1833 38 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 47 126 (accept_3_4 37 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  47 126 (Polychromatic418967fa.accept_16_4_15_14_1_5056 36 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 47 126 (Polychromatic418967fa.accept_19_16_9_12_1_4792 35 47 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 126 (accept_3_4 34 47 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 47 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 47 126
  (Polychromatic418967fa.accept_20_12_7_6_1_6154 32 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 47 126 (accept_3_4 31 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  47 126 (Polychromatic418967fa.accept_11_8_3_5_1_355 30 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 47 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 47 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 126 (accept_3_4 28 47 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 126 (Polychromatic418967fa.accept_13_1_8_9_1_1154 27 47 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 47 126
  (Polychromatic418967fa.accept_15_11_2_6_1_3010 26 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 47 126 (accept_3_4 25 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  47 126 (Polychromatic418967fa.accept_13_11_8_9_1_1161 24 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 47 126 (Polychromatic418967fa.accept_10_3_7_6_1_659 23 47 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 126 (accept_3_4 22 47 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 47 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 47 126
  (Polychromatic418967fa.accept_13_7_8_9_1_1158 20 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 47 126 (accept_3_4 19 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  47 126 (Polychromatic418967fa.accept_19_18_9_12_1_6153 18 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 47 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 47 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 126 (accept_3_4 16 47 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 126 (Polychromatic418967fa.accept_28_15_19_14_1_893 15 47 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 126
  (Polychromatic418967fa.accept_13_1_8_9_1_1154 14 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 47 126 (accept_3_4 13 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  47 126 (Polychromatic418967fa.accept_13_12_8_9_1_1833 12 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 47 126 (Polychromatic418967fa.accept_10_1_7_6_1_91 11 47 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 126 (accept_3_4 10 47 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 47 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 47 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 126
  (Polychromatic418967fa.accept_11_8_3_5_1_355 8 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 47 126 (accept_3_4 7 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47
  126 (Polychromatic418967fa.accept_17_6_13_7_1_272 6 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 47 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 47 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 126 (accept_3_4 4 47 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 47 126 (Polychromatic418967fa.accept_10_3_7_6_1_659 3 47 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 126
  (Polychromatic418967fa.accept_17_2_13_7_1_5011 2 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 47 126 (accept_3_4 1 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47
  126))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 126 (allA_succ_of_accept 45 46 126
  (Polychromatic418967fa.accept_12_9_10_6_1_872 45 46 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 46 126 2 22 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 46 126 (Polychromatic418967fa.accept_13_4_7_9_1_5260 43 46 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 46 126 2 21 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 46 126 (accept_3_5 41 46 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 46 126 2 20 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 46 126 (Polychromatic418967fa.accept_12_3_10_6_1_442 39 46 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 46 126 2 19 23 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 46 126
  (Polychromatic418967fa.accept_13_11_7_9_1_612 37 46 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 46 126 2 18 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 46 126 (accept_3_5 35 46 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 46
  126 2 17 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  46 126 (Polychromatic418967fa.accept_12_9_10_6_1_872 33 46 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 46 126 2 16 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 46 126 (Polychromatic418967fa.accept_22_9_2_16_1_6152 31 46 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 46 126 2 15 23 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 46 126 (accept_3_5 29 46 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 46 126 2 14 23 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 46 126
  (Polychromatic418967fa.accept_12_3_10_6_1_442 27 46 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 46 126 2 13 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 46 126 (Polychromatic418967fa.accept_15_10_1_6_1_3033 25 46 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 46 126 2 12 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 46 126 (accept_3_5 23 46 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 46 126 2 11 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 46 126 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 46 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 46 126 2 10 23 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 46 126
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 19 46 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 46 126 2 9 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 46 126 (accept_3_5 17 46 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 46
  126 2 8 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  46 126 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 46 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 46 126 2 7 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 46 126 (Polychromatic418967fa.accept_22_13_2_16_1_6151 13 46 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 126 2 6 23 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 126 (accept_3_5 11 46 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46 126 2 5 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 46 126 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 46 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 46 126 2 4 23 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 46 126
  (Polychromatic418967fa.accept_15_7_1_6_1_6150 7 46 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 46 126 2 3 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 46 126 (accept_3_5 5 46 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 46 126
  2 2 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 46
  126 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 46 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 46 126 2 1 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 46 126 (Polychromatic418967fa.accept_19_1_8_12_1_6149 1 46 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46 126)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45
  126 (allA_succ_of_accept 44 45 126 (Polychromatic418967fa.accept_10_4_5_6_1_651 44 45 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 45 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 45 126 3 14 15 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 45 126
  (Polychromatic418967fa.accept_10_1_5_6_1_649 41 45 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 45 126 (Polychromatic418967fa.accept_12_4_9_6_1_440 40 45 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 45 126 3 13 15 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 45 126 (Polychromatic418967fa.accept_12_2_9_6_1_439 38
  45 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 126
  (Polychromatic418967fa.accept_19_18_7_12_1_6148 37 45 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 45 126 9 4 5 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 45 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 45 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 126 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 45 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 45 126 3 11 15 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 45 126
  (Polychromatic418967fa.accept_12_8_9_6_1_127 32 45 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 45 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45 126 3 10 15 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 126 (Polychromatic418967fa.accept_10_9_5_6_1_691 29
  45 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 126
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 28 45 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 45 126 9 3 5 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 45 126 (Polychromatic418967fa.accept_12_2_9_6_1_439 26 45 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 126 (Polychromatic418967fa.accept_23_2_22_11_1_6147 25 45
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 45 126 3 8 15 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 126
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 45 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 45 126 (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 45 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 45 126 3 7 15 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 45 126 (Polychromatic418967fa.accept_12_8_9_6_1_127 20 45 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 126
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 45 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 45 126 9 2 5 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 45 126 (Polychromatic418967fa.accept_11_6_1_5_1_2388 17 45 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 126 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 45 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 126 3 5 15 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 126
  (Polychromatic418967fa.accept_10_4_5_6_1_651 14 45 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 126 (Polychromatic418967fa.accept_17_13_11_7_1_4961 13 45 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 45 126 3 4 15 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 45 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 45 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 126
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 45 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 45 126 9 1 5 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 45 126 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 45 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 45 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 126 3 2 15 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 45 126
  (Polychromatic418967fa.accept_17_5_11_7_1_6146 5 45 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 45 126 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 45 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 45 126 3 1 15 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 45 126 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 45 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 126
  (Polychromatic418967fa.accept_10_1_5_6_1_649 1 45 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 45 126))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 126 (allA_succ_of_accept 43 44 126
  (accept_3_4 43 44 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 44 126 2 21 22 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 44 126
  (Polychromatic418967fa.accept_13_2_5_9_1_610 41 44 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 44 126 2 20 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 44 126 (Polychromatic418967fa.accept_12_3_8_6_1_895 39 44 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 126 2 19 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 126 (accept_3_4 37 44 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 126 2 18 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44 126 (Polychromatic418967fa.accept_10_5_4_6_1_319 35 44 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 44 126 2 17 22 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 44 126
  (Polychromatic418967fa.accept_12_9_8_6_1_466 33 44 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 44 126 2 16 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 44 126 (accept_3_4 31 44 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44
  126 2 15 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  44 126 (Polychromatic418967fa.accept_13_3_5_9_1_5285 29 44 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 44 126 2 14 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 44 126 (Polychromatic418967fa.accept_12_3_8_6_1_895 27 44 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 44 126 2 13 22 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 44 126 (accept_3_4 25 44 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 44 126 2 12 22 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 44 126
  (Polychromatic418967fa.accept_15_8_14_6_1_3003 23 44 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 44 126 2 11 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 44 126 (Polychromatic418967fa.accept_12_9_8_6_1_466 21 44 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 44 126 2 10 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 44 126 (accept_3_4 19 44 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44 126 2 9 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 44 126 (Polychromatic418967fa.accept_13_4_5_9_1_1829 17 44 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 44 126 2 8 22 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 44 126
  (Polychromatic418967fa.accept_10_5_4_6_1_319 15 44 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 44 126 2 7 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 44 126 (accept_3_4 13 44 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44
  126 2 6 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  44 126 (Polychromatic418967fa.accept_25_11_19_1_1_6145 11 44 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 44 126 2 5 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 44 126 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 44 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 44 126 2 4 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 44 126 (accept_3_4 7 44 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 126 2 3 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 44 126 (Polychromatic418967fa.accept_10_5_4_6_1_319 5 44 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 44 126 2 2 22 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 44 126
  (Polychromatic418967fa.accept_12_3_8_6_1_895 3 44 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 44 126 2 1 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 44 126 (accept_3_4 1 44 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44
  126)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 126 (allA_succ_of_accept 42 43 126
  (Polychromatic418967fa.accept_19_4_5_12_1_3441 42 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 126 (accept_3_5 41 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 126 (Polychromatic418967fa.accept_27_13_16_18_1_6144 40 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 126 (Polychromatic418967fa.accept_10_9_3_6_1_686 39 43 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 126 (accept_3_5 38 43 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 43 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 126
  (Polychromatic418967fa.accept_17_2_9_7_1_5002 36 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 126 (accept_3_5 35 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 126 (Polychromatic418967fa.accept_13_8_4_9_1_1145 34 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 43 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 126 (accept_3_5 32 43 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 126 (Polychromatic418967fa.accept_13_5_4_9_1_601 31 43 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 126
  (Polychromatic418967fa.accept_19_11_5_12_1_3439 30 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 126 (accept_3_5 29 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 126 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 126 (Polychromatic418967fa.accept_10_7_3_6_1_644 27 43 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 126 (accept_3_5 26 43 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 43 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 126
  (Polychromatic418967fa.accept_26_24_17_22_1_6143 24 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 43 126 (accept_3_5 23 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 43 126 (Polychromatic418967fa.accept_15_7_13_6_1_696 22 43 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 43 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 126 (accept_3_5 20 43 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 126 (Polychromatic418967fa.accept_10_9_3_6_1_686
  19 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 126
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 126 (accept_3_5 17 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 126 (Polychromatic418967fa.accept_19_16_5_12_1_6142 16 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 126 (Polychromatic418967fa.accept_11_4_10_5_1_1202 15 43 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 126 (accept_3_5 14 43 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 43 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 126
  (Polychromatic418967fa.accept_23_12_20_11_1_6141 12 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 43 126 (accept_3_5 11 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 43 126 (Polychromatic418967fa.accept_23_10_20_11_1_6140 10 43 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 43 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 126 (accept_3_5 8 43 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 126 (Polychromatic418967fa.accept_10_7_3_6_1_644 7
  43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 126
  (Polychromatic418967fa.accept_11_6_10_5_1_341 6 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 126 (accept_3_5 5 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  126 (Polychromatic418967fa.accept_11_4_10_5_1_1202 4 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 43 126 (Polychromatic418967fa.accept_16_3_11_14_1_446 3 43 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 126 (accept_3_5 2 43 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 43 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 126)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 42 126 (allA_succ_of_accept 41 42 126 (Polychromatic418967fa.accept_10_1_2_6_1_638 41 42 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42 126 2 20 21 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 42 126 3 13 14 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 42 126 2 19 21 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 126
  (Polychromatic418967fa.accept_15_7_12_6_1_1327 37 42 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 42 126 6 6 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 42 126 7 5 6 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 34 42 126 2 17 21 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 42 126 3 11 14 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 42 126 2 16 21 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 42 126 (Polychromatic418967fa.accept_10_1_2_6_1_638 31 42 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 126 6 5 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 126 (Polychromatic418967fa.accept_11_7_9_5_1_338 29 42 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 126 14 2 3 9 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 42 126 3 9 14 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 42 126 2 13 21 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 126
  (Polychromatic418967fa.accept_13_12_3_9_1_4341 25 42 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 126 6 4 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 42 126 (Polychromatic418967fa.accept_16_7_10_14_1_1884 23 42 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 126 2 11 21 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 42 126 21 1 2 6 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 42 126 2 10 21 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 42 126 (Polychromatic418967fa.accept_13_6_3_9_1_1827
  19 42 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 126 6 3 7 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 126
  (Polychromatic418967fa.accept_15_2_12_6_1_3063 17 42 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 42 126 2 8 21 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 42 126 3 5 14 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 42 126 14 1 3 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 42 126 (Polychromatic418967fa.accept_16_13_10_14_1_2871 13 42 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 126 6 2 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 126 (Polychromatic418967fa.accept_10_1_2_6_1_638 11 42 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 126 2 5 21 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 42 126 3 3 14 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 42 126 2 4 21 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 42 126 7 1 6 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 42 126 6 1 7 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 126
  (Polychromatic418967fa.accept_13_5_3_9_1_1189 5 42 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 42 126 2 2 21 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 42 126 3 1 14 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 42 126 2 1 21 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 42 126 (Polychromatic418967fa.accept_10_1_2_6_1_638 1 42 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 42 126)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 126
  (allA_succ_of_accept 40 41 126 (accept_3_4 40 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  41 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 41 126 (Polychromatic418967fa.accept_24_14_17_6_1_6139 38 41 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 126 (accept_3_4 37 41 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 41 126 (Polychromatic418967fa.accept_11_3_8_5_1_336 36 41 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 126
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 126 (accept_3_4 34 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 126 (Polychromatic418967fa.accept_13_7_2_9_1_1826 33 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 126 (Polychromatic418967fa.accept_10_2_1_6_1_634 32 41 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 126 (accept_3_4 31 41 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 126 (Polychromatic418967fa.accept_19_11_3_12_1_6138 30 41 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 126
  (Polychromatic418967fa.accept_13_3_2_9_1_1187 29 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 126 (accept_3_4 28 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 126 (Polychromatic418967fa.accept_19_7_3_12_1_4787 26 41 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 126 (accept_3_4 25 41 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 126 (Polychromatic418967fa.accept_11_2_8_5_1_1219 24 41 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 126
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 126 (accept_3_4 22 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 126 (Polychromatic418967fa.accept_16_5_9_14_1_5051 21 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 126 (Polychromatic418967fa.accept_13_7_2_9_1_1826 20 41 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 126 (accept_3_4 19 41 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 126 (Polychromatic418967fa.accept_13_5_2_9_1_1195 18 41 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 126
  (Polychromatic418967fa.accept_10_7_1_6_1_673 17 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 126 (accept_3_4 16 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 126 (Polychromatic418967fa.accept_11_3_8_5_1_336 14 41 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 126 (accept_3_4 13 41 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 126 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 41 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 126
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 126 (accept_3_4 10 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 126 (Polychromatic418967fa.accept_15_9_11_6_1_637 9 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 126 (Polychromatic418967fa.accept_22_8_19_16_1_6137 8 41 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 126 (accept_3_4 7 41 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 126 (Polychromatic418967fa.accept_13_6_2_9_1_1188 6 41 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 126
  (Polychromatic418967fa.accept_10_5_1_6_1_672 5 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 126 (accept_3_4 4 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  126 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 126 (Polychromatic418967fa.accept_10_2_1_6_1_634 2 41 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 126 (accept_3_4 1 41 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 126))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 126 (allA_succ_of_accept 39 40 126
  (Polychromatic418967fa.accept_12_3_4_6_1_434 39 40 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 40 126 2 19 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 40 126 (Polychromatic418967fa.accept_13_11_1_9_1_1179 37 40 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 40 126 2 18 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 40 126 (accept_3_5 35 40 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 40 126 2 17 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 40 126 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 40 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 40 126 2 16 20 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 40 126
  (Polychromatic418967fa.accept_11_9_7_5_1_749 31 40 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 40 126 2 15 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 40 126 (accept_3_5 29 40 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 40
  126 2 14 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  40 126 (Polychromatic418967fa.accept_12_3_4_6_1_434 27 40 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 40 126 2 13 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 40 126 (Polychromatic418967fa.accept_19_6_2_12_1_6136 25 40 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 40 126 2 12 20 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 40 126 (accept_3_5 23 40 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 40 126 2 11 20 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 40 126
  (Polychromatic418967fa.accept_12_9_4_6_1_460 21 40 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 40 126 2 10 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 40 126 (Polychromatic418967fa.accept_13_6_1_9_1_619 19 40 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 40 126 2 9 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 40 126 (accept_3_5 17 40 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 40 126 2 8 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 40 126 (Polychromatic418967fa.accept_12_3_4_6_1_434 15 40 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 40 126 2 7 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 40 126 (Polychromatic418967fa.accept_17_13_6_7_1_4999
  13 40 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 40 126 2 6 20 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 40 126 (accept_3_5 11
  40 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40 126 2 5 20 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 40 126
  (Polychromatic418967fa.accept_11_9_7_5_1_749 9 40 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 40 126 2 4 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 40 126 (Polychromatic418967fa.accept_23_7_17_11_1_6135 7 40 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 40 126 2 3 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 40 126 (accept_3_5 5 40 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 40 126 2 2 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 40 126 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 40 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 40 126 2 1 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 40 126 (Polychromatic418967fa.accept_15_1_10_6_1_631 1
  40 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  126)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 126 (allA_succ_of_accept 38 39 126
  (Polychromatic418967fa.accept_12_2_3_6_1_112 38 39 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 39 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 126 3 12 13 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 126 (Polychromatic418967fa.accept_10_5_9_6_1_697 35
  39 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 126
  (Polychromatic418967fa.accept_11_1_6_5_1_1732 34 39 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 39 126 3 11 13 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 39 126 (Polychromatic418967fa.accept_11_10_6_5_1_1239 32 39 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 126 (Polychromatic418967fa.accept_15_1_9_6_1_1323 31 39 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 126 3 10 13 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 126
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 39 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 126 (Polychromatic418967fa.accept_12_4_3_6_1_879 28 39 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 126 3 9 13 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 126 (Polychromatic418967fa.accept_12_2_3_6_1_112 26 39 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 126
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 39 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 39 126 3 8 13 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 39 126 (Polychromatic418967fa.accept_10_3_9_6_1_94 23 39 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 126 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 39 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 126 3 7 13 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 126
  (Polychromatic418967fa.accept_12_8_3_6_1_909 20 39 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 126 (Polychromatic418967fa.accept_15_4_9_6_1_627 19 39 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 126 3 6 13 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 39 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 126
  (Polychromatic418967fa.accept_12_4_3_6_1_879 16 39 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 39 126 3 5 13 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 39 126 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 39 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 39 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 39 126 3 4 13 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 39 126
  (Polychromatic418967fa.accept_15_11_9_6_1_1321 11 39 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 126 (Polychromatic418967fa.accept_11_10_6_5_1_1239 10 39 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 126 3 3 13 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 126 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 39 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 126
  (Polychromatic418967fa.accept_19_7_1_12_1_6134 7 39 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 39 126 3 2 13 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 39 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 39 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 126 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 39 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 39 126 3 1 13 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 39 126
  (Polychromatic418967fa.accept_12_2_3_6_1_112 2 39 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 39 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 39 126))))))))))))))))))))))))))))))))))))))) (allB_succ 38 126
  (allA_succ_of_accept 37 38 126 (accept_3_4 37 38 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38
  126 2 18 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  38 126 (Polychromatic418967fa.accept_23_12_15_11_1_6133 35 38 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 38 126 2 17 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 38 126 (Polychromatic418967fa.accept_10_3_8_6_1_326 33 38 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 126 2 16 19 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 126 (accept_3_4 31 38 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 126 2 15 19 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 126
  (Polychromatic418967fa.accept_13_3_12_9_1_1193 29 38 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 126 2 14 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 38 126 (Polychromatic418967fa.accept_12_3_2_6_1_138 27 38 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 126 2 13 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 126 (accept_3_4 25 38 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 126 2 12 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 126 (Polychromatic418967fa.accept_10_3_8_6_1_326 23 38 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 38 126 2 11 19 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 38 126
  (Polychromatic418967fa.accept_12_9_2_6_1_455 21 38 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 38 126 2 10 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 38 126 (accept_3_4 19 38 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 38
  126 2 9 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  38 126 (Polychromatic418967fa.accept_15_2_8_6_1_1340 17 38 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 38 126 2 8 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 38 126 (Polychromatic418967fa.accept_12_3_2_6_1_138 15 38 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 126 2 7 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 126 (accept_3_4 13 38 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 126 2 6 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 38 126 (Polychromatic418967fa.accept_28_11_10_14_1_6132 11 38 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 38 126 2 5 19 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 38 126
  (Polychromatic418967fa.accept_12_9_2_6_1_455 9 38 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 38 126 2 4 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 38 126 (accept_3_4 7 38 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 38 126
  2 3 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 38
  126 (Polychromatic418967fa.accept_24_5_14_6_1_6131 5 38 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 38 126 2 2 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 38 126 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 38 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 126 2 1 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 126 (accept_3_4 1 38 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 38 126)))))))))))))))))))))))))))))))))))))) (allB_succ 37 126 (allA_succ_of_accept 36
  37 126 (Polychromatic418967fa.accept_19_17_18_12_1_4783 36 37 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 37 126 (accept_3_5 35 37 126 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 37 126 (Polychromatic418967fa.accept_13_8_11_9_1_593 34 37 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 126 (Polychromatic418967fa.accept_10_3_7_6_1_659 33 37 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 126 (accept_3_5 32 37 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 31
  37 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 126
  (Polychromatic418967fa.accept_19_11_18_12_1_4802 30 37 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 37 126 (accept_3_5 29 37 126 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 37 126 (Polychromatic418967fa.accept_13_2_11_9_1_591 28 37 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 37 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 126 (accept_3_5 26 37 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 126 (Polychromatic418967fa.accept_16_9_5_14_1_6126
  25 37 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 126
  (Polychromatic418967fa.accept_23_1_14_11_1_6130 24 37 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 126 (accept_3_5 23 37 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 126 (Polychromatic418967fa.accept_23_22_14_11_1_6129 22 37 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 126 (Polychromatic418967fa.accept_10_1_7_6_1_91 21 37 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 126 (accept_3_5 20 37 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 37 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 126
  (Polychromatic418967fa.accept_24_18_13_6_1_6128 18 37 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 126 (accept_3_5 17 37 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 126 (Polychromatic418967fa.accept_15_1_7_6_1_6127 16 37 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 37 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 126 (accept_3_5 14 37 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 126 (Polychromatic418967fa.accept_10_3_7_6_1_659 13 37 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 126
  (Polychromatic418967fa.accept_15_12_7_6_1_4013 12 37 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 126 (accept_3_5 11 37 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 126 (Polychromatic418967fa.accept_11_10_4_5_1_359 10 37 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 126 (Polychromatic418967fa.accept_16_9_5_14_1_6126 9 37 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 126 (accept_3_5 8 37 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 37 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 126
  (Polychromatic418967fa.accept_19_6_18_12_1_6125 6 37 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 126 (accept_3_5 5 37 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  126 (Polychromatic418967fa.accept_17_4_3_7_1_4971 4 37 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 37 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 37 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 126 (accept_3_5 2 37 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 37 126 (Polychromatic418967fa.accept_10_1_7_6_1_91 1 37 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 126))))))))))))))))))))))))))))))))))))) (allB_succ
  36 126 (allA_succ_of_accept 35 36 126 (Polychromatic418967fa.accept_22_13_14_16_1_6124 35 36 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36 126 2 17 18 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 36 126 3 11 12 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 36 126 2 16 18 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 126
  (Polychromatic418967fa.accept_16_15_4_14_1_6123 31 36 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 36 126 6 5 6 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 36 126 (Polychromatic418967fa.accept_17_12_2_7_1_3813 29 36 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 126 2 14 18 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 36 126 9 3 4 14 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 36 126 2 13 18 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 36 126 (Polychromatic418967fa.accept_13_12_10_9_1_1166
  25 36 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 126 6 4 6 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 126
  (Polychromatic418967fa.accept_16_7_4_14_1_2860 23 36 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 36 126 2 11 18 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 36 126 3 7 12 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 36 126 2 10 18 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 36 126 (Polychromatic418967fa.accept_11_8_3_5_1_355 19 36 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 126 18 1 2 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 126 (Polychromatic418967fa.accept_16_1_4_14_1_1896 17 36 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 126 2 8 18 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 36 126 3 5 12 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 36 126 2 7 18 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 126
  (Polychromatic418967fa.accept_17_13_2_7_1_6122 13 36 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 36 126 6 2 6 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 36 126 (Polychromatic418967fa.accept_20_11_16_6_1_6121 11 36 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36 126 2 5 18 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 36 126 9 1 4 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 36 126 2 4 18 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 126 (Polychromatic418967fa.accept_16_7_4_14_1_2860 7 36 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 126 6 1 6 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 126
  (Polychromatic418967fa.accept_19_5_17_12_1_6120 5 36 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 36 126 2 2 18 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 36 126 3 1 12 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 36 126 2 1 18 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 36 126 (Polychromatic418967fa.accept_13_1_10_9_1_215 1 36 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 36 126)))))))))))))))))))))))))))))))))))) (allB_succ 35 126
  (allA_succ_of_accept 34 35 126 (accept_3_4 34 35 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  35 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 35 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 35 126 (Polychromatic418967fa.accept_19_13_16_12_1_6096 32 35 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 126 (accept_3_4 31 35 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 35 126 (Polychromatic418967fa.accept_11_8_2_5_1_1769 30 35 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 126
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 35 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 35 126 7 4 5 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 35 126 (Polychromatic418967fa.accept_15_12_5_6_1_2148 27 35 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 126 (Polychromatic418967fa.accept_15_11_5_6_1_669 26 35 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 126 (accept_3_4 25 35 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 35 126 (Polychromatic418967fa.accept_10_4_5_6_1_651
  24 35 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 126
  (Polychromatic418967fa.accept_19_4_16_12_1_485 23 35 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 126 (accept_3_4 22 35 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 35
  126 7 3 5 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20
  35 126 (Polychromatic418967fa.accept_23_20_12_11_1_6119 20 35 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 35 126 (accept_3_4 19 35 126 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 35 126 (Polychromatic418967fa.accept_15_3_5_6_1_4005 18 35 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 35 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 126 (accept_3_4 16 35 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 126
  (Polychromatic418967fa.accept_19_15_16_12_1_4779 15 35 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 35 126 7 2 5 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 35 126 (accept_3_4 13 35 126 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 35 126 (Polychromatic418967fa.accept_15_12_5_6_1_2148 12 35 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 126 (Polychromatic418967fa.accept_10_1_5_6_1_649 11 35 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 126 (accept_3_4 10 35 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 35
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 126
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 8 35 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 35 126 7 1 5 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 35 126 (Polychromatic418967fa.accept_19_6_16_12_1_6118 6 35 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 35 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 126 (accept_3_4 4 35 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 126 (Polychromatic418967fa.accept_15_3_5_6_1_4005 3
  35 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 126
  (Polychromatic418967fa.accept_22_2_13_16_1_6117 2 35 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 126 (accept_3_4 1 35 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  126))))))))))))))))))))))))))))))))))) (allB_succ 34 126 (allA_succ_of_accept 33 34 126
  (Polychromatic418967fa.accept_12_9_10_6_1_872 33 34 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 34 126 2 16 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 34 126 (Polychromatic418967fa.accept_20_11_14_6_1_4714 31 34 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 34 126 2 15 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 34 126 (accept_3_5 29 34 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 34 126 2 14 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 34 126 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 34 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 34 126 2 13 17 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 34 126
  (Polychromatic418967fa.accept_10_5_4_6_1_319 25 34 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 34 126 2 12 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 34 126 (accept_3_5 23 34 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34
  126 2 11 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  34 126 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 34 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 34 126 2 10 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 34 126 (Polychromatic418967fa.accept_20_19_14_6_1_4726 19 34 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 34 126 2 9 17 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 34 126 (accept_3_5 17 34 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 34 126 2 8 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 34 126 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 34 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 34 126 2 7 17 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 34 126
  (Polychromatic418967fa.accept_15_13_4_6_1_3046 13 34 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 34 126 2 6 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 34 126 (accept_3_5 11 34 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34
  126 2 5 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  34 126 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 34 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 34 126 2 4 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 34 126 (Polychromatic418967fa.accept_13_7_8_9_1_1158 7 34 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 126 2 3 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 126 (accept_3_5 5 34 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 34 126 2 2 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 34 126 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 34 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 126 2 1 17 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 126
  (Polychromatic418967fa.accept_13_1_8_9_1_1154 1 34 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 34 126)))))))))))))))))))))))))))))))))) (allB_succ 33 126 (allA_succ_of_accept 32 33 126
  (Polychromatic418967fa.accept_12_8_9_6_1_127 32 33 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 33 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 33 126 3 10 11 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 33 126 (Polychromatic418967fa.accept_10_9_3_6_1_686 29
  33 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 126
  (Polychromatic418967fa.accept_10_8_3_6_1_685 28 33 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 33 126 3 9 11 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 33 126 (Polychromatic418967fa.accept_12_2_9_6_1_439 26 33 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 126 (Polychromatic418967fa.accept_15_10_3_6_1_3042 25 33
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 126 3 8 11 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 126
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 33 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 33 126 (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 33 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 33 126 3 7 11 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 33 126 (Polychromatic418967fa.accept_12_8_9_6_1_127 20 33 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 126
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 33 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 33 126 3 6 11 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 33 126 (Polychromatic418967fa.accept_10_7_3_6_1_644 17 33 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 126 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 33 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 126 3 5 11 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 126
  (Polychromatic418967fa.accept_12_2_9_6_1_439 14 33 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 126 (Polychromatic418967fa.accept_16_13_1_14_1_2855 13 33 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 33 126 3 4 11 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 33 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 33 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 126
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 33 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 33 126 3 3 11 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 33 126 (Polychromatic418967fa.accept_10_8_3_6_1_685 8 33 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 33 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 126 3 2 11 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 126
  (Polychromatic418967fa.accept_15_5_3_6_1_2128 5 33 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 33 126 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 33 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 33 126 3 1 11 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 33 126 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 33 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 126
  (Polychromatic418967fa.accept_15_1_3_6_1_621 1 33 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 33 126))))))))))))))))))))))))))))))))) (allB_succ 32 126 (allA_succ_of_accept 31 32 126 (accept_3_4 31 32
  126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32 126 2 15 16 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 32 126
  (Polychromatic418967fa.accept_13_3_6_9_1_1150 29 32 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 32 126 2 14 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 32 126 (Polychromatic418967fa.accept_12_3_8_6_1_895 27 32 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 126 2 13 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 126 (accept_3_4 25 32 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 126 2 12 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 32 126 (Polychromatic418967fa.accept_13_10_6_9_1_1152 23 32 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 126 2 11 16 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 126
  (Polychromatic418967fa.accept_10_1_2_6_1_638 21 32 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 32 126 2 10 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 32 126 (accept_3_4 19 32 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32
  126 2 9 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  32 126 (Polychromatic418967fa.accept_11_6_10_5_1_341 17 32 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 32 126 2 8 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 32 126 (Polychromatic418967fa.accept_11_4_10_5_1_1202 15 32 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 126 2 7 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 126 (accept_3_4 13 32 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32 126 2 6 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 32 126 (Polychromatic418967fa.accept_10_1_2_6_1_638 11 32 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 32 126 2 5 16 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 32 126
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 32 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 32 126 2 4 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 32 126 (accept_3_4 7 32 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 126
  2 3 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 32
  126 (Polychromatic418967fa.accept_17_5_15_7_1_4992 5 32 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 32 126 2 2 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 32 126 (Polychromatic418967fa.accept_12_3_8_6_1_895 3 32 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 32 126 2 1 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 32 126 (accept_3_4 1 32 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 32 126)))))))))))))))))))))))))))))))) (allB_succ 31 126 (allA_succ_of_accept 30 31 126
  (Polychromatic418967fa.accept_13_4_5_9_1_1829 30 31 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 126 (accept_3_5 29 31 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  31 126 (Polychromatic418967fa.accept_13_2_5_9_1_610 28 31 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 126 (Polychromatic418967fa.accept_10_7_1_6_1_673 27 31 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 126 (accept_3_5 26 31 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 31 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 126
  (Polychromatic418967fa.accept_15_9_1_6_1_657 24 31 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 126 (accept_3_5 23 31 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 126 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 31 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 31 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 126 (accept_3_5 20 31 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 126 (Polychromatic418967fa.accept_23_19_8_11_1_6116 19 31 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 126
  (Polychromatic418967fa.accept_11_7_9_5_1_338 18 31 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 126 (accept_3_5 17 31 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 126 (Polychromatic418967fa.accept_13_3_5_9_1_5285 16 31 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 126 (Polychromatic418967fa.accept_10_5_1_6_1_672 15 31 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 126 (accept_3_5 14 31 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 31 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 126
  (Polychromatic418967fa.accept_10_2_1_6_1_634 12 31 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 126 (accept_3_5 11 31 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 126 (Polychromatic418967fa.accept_15_10_1_6_1_3033 10 31 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 31 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 126 (accept_3_5 8 31 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 126 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 31 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 126
  (Polychromatic418967fa.accept_17_6_14_7_1_6115 6 31 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 126 (accept_3_5 5 31 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  126 (Polychromatic418967fa.accept_13_4_5_9_1_1829 4 31 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 31 126 (Polychromatic418967fa.accept_13_3_5_9_1_5285 3 31 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 126 (accept_3_5 2 31 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 31 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 126))))))))))))))))))))))))))))))) (allB_succ 30 126
  (allA_succ_of_accept 29 30 126 (Polychromatic418967fa.accept_19_10_11_12_1_6114 29 30 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30 126 2 14 15 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 30 126 3 9 10 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 30 126 2 13 15 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 30 126 (Polychromatic418967fa.accept_11_3_8_5_1_336 25
  30 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 126 6 4 5 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 126
  (Polychromatic418967fa.accept_17_6_13_7_1_272 23 30 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 30 126 2 11 15 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 30 126 3 7 10 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 30 126 2 10 15 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 126 (Polychromatic418967fa.accept_13_6_4_9_1_4326 19 30 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 126 6 3 5 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 126 (Polychromatic418967fa.accept_23_17_7_11_1_6113 17 30
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 126 2 8 15 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 30 126 3 5 10 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 30 126 2 7 15 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 126
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 13 30 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 30 126 6 2 5 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 30 126 (Polychromatic418967fa.accept_17_11_13_7_1_3795 11 30 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 126 2 5 15 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 30 126 3 3 10 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 30 126 2 4 15 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 126 (Polychromatic418967fa.accept_13_7_4_9_1_1865 7 30 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 126 6 1 5 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 126
  (Polychromatic418967fa.accept_13_5_4_9_1_601 5 30 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 30 126 2 2 15 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 30 126 3 1 10 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 30 126 2 1 15 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 30 126 (Polychromatic418967fa.accept_19_1_11_12_1_6112 1 30 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 30 126)))))))))))))))))))))))))))))) (allB_succ 29 126 (allA_succ_of_accept
  28 29 126 (accept_3_4 28 29 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 126
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 29 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 126 (Polychromatic418967fa.accept_16_10_13_14_1_5042 26 29 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 126 (accept_3_4 25 29 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 126 (Polychromatic418967fa.accept_15_9_14_6_1_3004 24 29 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 126
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 29 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 126 (accept_3_4 22 29 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 126 (Polychromatic418967fa.accept_13_8_3_9_1_5269 21 29 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 126 (Polychromatic418967fa.accept_11_9_7_5_1_749 20 29 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 126 (accept_3_4 19 29 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 126 (Polychromatic418967fa.accept_13_5_3_9_1_1189 18 29 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 126
  (Polychromatic418967fa.accept_16_1_13_14_1_1064 17 29 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 126 (accept_3_4 16 29 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 29 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 126 (Polychromatic418967fa.accept_19_14_10_12_1_4809 14 29 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 126 (accept_3_4 13 29 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 126 (Polychromatic418967fa.accept_13_12_3_9_1_4341 12 29
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 126
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 29 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 126 (accept_3_4 10 29 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 126 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 29 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 126 (Polychromatic418967fa.accept_13_8_3_9_1_5269 8 29 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 126 (accept_3_4 7 29 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 126 (Polychromatic418967fa.accept_13_6_3_9_1_1827 6 29 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 126
  (Polychromatic418967fa.accept_10_5_9_6_1_697 5 29 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 126 (accept_3_4 4 29 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  126 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 29 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 126 (Polychromatic418967fa.accept_13_2_3_9_1_2610 2 29 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 126 (accept_3_4 1 29 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 126))))))))))))))))))))))))))))) (allB_succ 28 126 (allA_succ_of_accept 27 28 126
  (Polychromatic418967fa.accept_12_3_4_6_1_434 27 28 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 28 126 2 13 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 28 126 (Polychromatic418967fa.accept_26_25_2_22_1_6111 25 28 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 126 2 12 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 126 (accept_3_5 23 28 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 28 126 2 11 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 28 126 7 3 4 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 28 126 2 10 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 28 126 (Polychromatic418967fa.accept_13_6_2_9_1_1188 19 28 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 28 126 2 9 14 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 28 126 (accept_3_5 17 28 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 28 126 2 8 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 28 126 (Polychromatic418967fa.accept_12_3_4_6_1_434 15
  28 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 28 126 14 1 2 9 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 28 126
  (Polychromatic418967fa.accept_10_3_8_6_1_326 13 28 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 28 126 2 6 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 28 126 (accept_3_5 11 28 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 28
  126 2 5 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  28 126 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 28 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 28 126 2 4 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 7 28 126 7 1 4 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 6 28 126 2 3 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 28 126 (accept_3_5 5 28 126 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 28 126 2 2 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 28 126 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 28 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 28 126 2 1 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 28 126 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1 28 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 126)))))))))))))))))))))))))))) (allB_succ
  27 126 (allA_succ_of_accept 26 27 126 (Polychromatic418967fa.accept_12_2_3_6_1_112 26 27 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 25
  27 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 27 126 3 8 9 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 27 126
  (Polychromatic418967fa.accept_10_3_7_6_1_659 23 27 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 27 126 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 27 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 27 126 3 7 9 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 27 126 (Polychromatic418967fa.accept_12_8_3_6_1_909 20 27 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 126
  (Polychromatic418967fa.accept_13_6_1_9_1_619 19 27 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 27 126 9 2 3 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 27 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 27 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 126 (Polychromatic418967fa.accept_12_4_3_6_1_879 16 27 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 27 126 3 5 9 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 27 126
  (Polychromatic418967fa.accept_12_2_3_6_1_112 14 27 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 27 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 27 126 3 4 9 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 27 126 (Polychromatic418967fa.accept_10_1_7_6_1_91 11 27 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 126
  (Polychromatic418967fa.accept_12_10_3_6_1_882 10 27 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 27 126 9 1 3 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 27 126 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 27 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 126 (Polychromatic418967fa.accept_15_7_12_6_1_1327 7 27 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 27 126 3 2 9 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 27 126
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 27 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 27 126 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 27 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 27 126 3 1 9 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 27 126 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 27 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 126
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 27 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 27 126))))))))))))))))))))))))))) (allB_succ 26 126 (allA_succ_of_accept 25 26 126 (accept_3_4 25 26 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26 126 2 12 13 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 26 126
  (Polychromatic418967fa.accept_16_7_10_14_1_1884 23 26 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 26 126 2 11 13 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 26 126 (Polychromatic418967fa.accept_11_10_4_5_1_359 21 26 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 126 2 10 13 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 126 (accept_3_4 19 26 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 126 2 9 13 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 26 126 (Polychromatic418967fa.accept_15_2_11_6_1_2135 17 26 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 26 126 2 8 13 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 26 126
  (Polychromatic418967fa.accept_12_3_2_6_1_138 15 26 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 26 126 2 7 13 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 26 126 (accept_3_4 13 26 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26
  126 2 6 13 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  26 126 (Polychromatic418967fa.accept_19_11_7_12_1_4770 11 26 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 26 126 2 5 13 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 26 126 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 26 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 26 126 2 4 13 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 26 126 (accept_3_4 7 26 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 126 2 3 13 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 26 126 (Polychromatic418967fa.accept_15_5_11_6_1_692 5 26 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 26 126 2 2 13 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 26 126
  (Polychromatic418967fa.accept_12_3_2_6_1_138 3 26 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 26 126 2 1 13 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 26 126 (accept_3_4 1 26 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  126)))))))))))))))))))))))))) (allB_succ 25 126 (allA_succ_of_accept 24 25 126
  (Polychromatic418967fa.accept_10_4_5_6_1_651 24 25 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 126 (accept_3_5 23 25 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 126 (Polychromatic418967fa.accept_23_22_2_11_1_6110 22 25 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 126 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 25 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 126 (accept_3_5 20 25 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 25 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 126
  (Polychromatic418967fa.accept_15_3_10_6_1_632 18 25 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 126 (accept_3_5 17 25 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 126 (Polychromatic418967fa.accept_13_3_12_9_1_1193 16 25 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 25 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 126 (accept_3_5 14 25 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 126 (Polychromatic418967fa.accept_19_13_6_12_1_6109 13 25 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 126
  (Polychromatic418967fa.accept_15_12_10_6_1_2134 12 25 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 126 (accept_3_5 11 25 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 126 (Polychromatic418967fa.accept_13_10_12_9_1_1837 10 25 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 126 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 25 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 126 (accept_3_5 8 25 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 25 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 126
  (Polychromatic418967fa.accept_27_6_25_18_1_6108 6 25 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 126 (accept_3_5 5 25 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  126 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 25 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 25 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 25 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 126 (accept_3_5 2 25 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 25 126 (Polychromatic418967fa.accept_10_1_5_6_1_649 1 25 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 126))))))))))))))))))))))))) (allB_succ 24 126
  (allA_succ_of_accept 23 24 126 (Polychromatic418967fa.accept_19_4_5_12_1_3441 23 24 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 126 2 11 12 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 24 126 3 7 8 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 24 126 2 10 12 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 24 126 (Polychromatic418967fa.accept_11_8_2_5_1_1769
  19 24 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 126 6 3 4 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 126
  (Polychromatic418967fa.accept_19_17_5_12_1_4753 17 24 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 24 126 2 8 12 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 24 126 3 5 8 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 24 126 2 7 12 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 24 126 (Polychromatic418967fa.accept_19_13_5_12_1_6107 13 24 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 126 6 2 4 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 126 (Polychromatic418967fa.accept_15_11_9_6_1_1321 11 24 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 126 2 5 12 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 24 126 3 3 8 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 24 126 2 4 12 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 24 126
  (Polychromatic418967fa.accept_13_7_11_9_1_1858 7 24 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 24 126 6 1 4 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 24 126 (Polychromatic418967fa.accept_10_5_4_6_1_319 5 24 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 126 2 2 12 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 24 126 3 1 8 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 24 126 2 1 12 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 126 (Polychromatic418967fa.accept_13_1_11_9_1_1857 1 24 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 126)))))))))))))))))))))))) (allB_succ 23
  126 (allA_succ_of_accept 22 23 126 (accept_3_4 22 23 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 23 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 23 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 23 126 (Polychromatic418967fa.accept_16_4_7_14_1_3897 20 23 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 126 (accept_3_4 19 23 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 23 126 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 23 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 126
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 23 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 23 126 (accept_3_4 16 23 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  23 126 (Polychromatic418967fa.accept_16_15_7_14_1_2883 15 23 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 23 126 (Polychromatic418967fa.accept_13_1_10_9_1_215 14 23 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 126 (accept_3_4 13 23 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 23 126 (Polychromatic418967fa.accept_13_12_10_9_1_1166 12 23 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 126
  (Polychromatic418967fa.accept_19_11_4_12_1_6106 11 23 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 126 (accept_3_4 10 23 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  23 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 23 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 23 126 (Polychromatic418967fa.accept_10_8_3_6_1_685 8 23 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 126 (accept_3_4 7 23 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 23 126 (Polychromatic418967fa.accept_11_6_1_5_1_2388 6 23 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 23
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 126 (accept_3_4 4 23 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23 126 (Polychromatic418967fa.accept_25_3_23_1_1_6105
  3 23 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 126
  (Polychromatic418967fa.accept_15_2_8_6_1_1340 2 23 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 23 126 (accept_3_4 1 23 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23
  126))))))))))))))))))))))) (allB_succ 22 126 (allA_succ_of_accept 21 22 126
  (Polychromatic418967fa.accept_10_1_2_6_1_638 21 22 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 22 126 2 10 11 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 22 126 (Polychromatic418967fa.accept_23_19_22_11_1_6104 19 22 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 22 126 2 9 11 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 22 126 (accept_3_5 17 22 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 22 126 2 8 11 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 22 126 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 22 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 22 126 2 7 11 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 22 126 (Polychromatic418967fa.accept_15_13_7_6_1_682
  13 22 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 22 126 2 6 11 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 22 126 (accept_3_5 11
  22 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 22 126 2 5 11 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 22 126
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 22 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 22 126 2 4 11 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 22 126 (Polychromatic418967fa.accept_19_7_3_12_1_4787 7 22 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 22 126 2 3 11 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 22 126 (accept_3_5 5 22 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 22 126 2 2 11 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 22 126 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 22 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 22 126 2 1 11 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 22 126 (Polychromatic418967fa.accept_10_1_2_6_1_638 1
  22 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 126)))))))))))))))))))))) (allB_succ
  21 126 (allA_succ_of_accept 20 21 126 (Polychromatic418967fa.accept_12_8_9_6_1_127 20 21 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 19
  21 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 126 3 6 7 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 126
  (Polychromatic418967fa.accept_10_7_1_6_1_673 17 21 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 126 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 21 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 21 126 3 5 7 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 21 126 7 2 3 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 21 126 (Polychromatic418967fa.accept_23_13_21_11_1_6103 13 21
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 21 126 3 4 7 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 21 126
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 21 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 126 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 21 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 126 3 3 7 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 126 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 21 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 21 126 7 1 3 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 21 126 3 2 7 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 21 126
  (Polychromatic418967fa.accept_10_5_1_6_1_672 5 21 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 21 126 (Polychromatic418967fa.accept_11_4_10_5_1_1202 4 21 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 21 126 3 1 7 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 21 126 (Polychromatic418967fa.accept_10_2_1_6_1_634 2 21 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 126
  (Polychromatic418967fa.accept_13_1_8_9_1_1154 1 21 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 21 126))))))))))))))))))))) (allB_succ 20 126 (allA_succ_of_accept 19 20 126 (accept_3_4 19 20 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 126 2 9 10 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 20 126 (Polychromatic418967fa.accept_13_4_7_9_1_5260 17 20 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 20 126 2 8 10 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 20 126
  (Polychromatic418967fa.accept_12_3_8_6_1_895 15 20 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 20 126 2 7 10 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 20 126 (accept_3_4 13 20 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 20
  126 2 6 10 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  20 126 (Polychromatic418967fa.accept_13_11_7_9_1_612 11 20 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 20 126 2 5 10 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 20 126 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 20 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 20 126 2 4 10 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 20 126 (accept_3_4 7 20 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 126 2 3 10 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 20 126 (Polychromatic418967fa.accept_19_5_1_12_1_6102 5 20 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 20 126 2 2 10 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 20 126
  (Polychromatic418967fa.accept_12_3_8_6_1_895 3 20 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 20 126 2 1 10 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 20 126 (accept_3_4 1 20 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20
  126)))))))))))))))))))) (allB_succ 19 126 (allA_succ_of_accept 18 19 126
  (Polychromatic418967fa.accept_24_18_19_6_1_6101 18 19 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 126 (accept_3_5 17 19 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 126 (Polychromatic418967fa.accept_13_3_6_9_1_1150 16 19 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 126 (Polychromatic418967fa.accept_10_5_9_6_1_697 15 19 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 126 (accept_3_5 14 19 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 19 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 126
  (Polychromatic418967fa.accept_17_12_2_7_1_3813 12 19 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 126 (accept_3_5 11 19 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 126 (Polychromatic418967fa.accept_13_10_6_9_1_1152 10 19 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 19 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 126 (accept_3_5 8 19 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 126 (Polychromatic418967fa.accept_13_7_6_9_1_1831 7 19 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 126
  (Polychromatic418967fa.accept_27_6_19_18_1_6100 6 19 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 126 (accept_3_5 5 19 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  126 (Polychromatic418967fa.accept_13_4_6_9_1_3401 4 19 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 19 126 (Polychromatic418967fa.accept_10_3_9_6_1_94 3 19 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 126 (accept_3_5 2 19 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 19 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 19 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 126))))))))))))))))))) (allB_succ 18 126
  (allA_succ_of_accept 17 18 126 (Polychromatic418967fa.accept_13_4_5_9_1_1829 17 18 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 126 2 8 9 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 18 126 3 5 6 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 18 126 2 7 9 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 18 126 (Polychromatic418967fa.accept_10_3_8_6_1_326 13 18 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 126 6 2 3 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 126
  (Polychromatic418967fa.accept_15_11_3_6_1_1306 11 18 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 18 126 2 5 9 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 18 126 9 1 2 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 18 126 2 4 9 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 18 126 (Polychromatic418967fa.accept_19_7_18_12_1_3427 7 18 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 126 6 1 3 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 126 (Polychromatic418967fa.accept_15_5_3_6_1_2128 5 18 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 126 2 2 9 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 18 126 3 1 6 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 18 126 2 1 9 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 18 126
  (Polychromatic418967fa.accept_13_1_5_9_1_226 1 18 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 18 126)))))))))))))))))) (allB_succ 17 126 (allA_succ_of_accept 16 17 126 (accept_3_4 16 17 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 17 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 126
  (Polychromatic418967fa.accept_19_14_17_12_1_6099 14 17 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 17 126 (accept_3_4 13 17 126 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 17 126 (Polychromatic418967fa.accept_11_1_6_5_1_1732 12 17 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 17 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 126 (accept_3_4 10 17 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 126 (Polychromatic418967fa.accept_20_9_17_6_1_6098
  9 17 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 126
  (Polychromatic418967fa.accept_13_8_4_9_1_1145 8 17 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 126 (accept_3_4 7 17 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  126 (Polychromatic418967fa.accept_13_6_4_9_1_4326 6 17 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 17 126 (Polychromatic418967fa.accept_13_5_4_9_1_601 5 17 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 126 (accept_3_4 4 17 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 17 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 17 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 126
  (Polychromatic418967fa.accept_19_2_17_12_1_6097 2 17 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 17 126 (accept_3_4 1 17 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17
  126))))))))))))))))) (allB_succ 16 126 (allA_succ_of_accept 15 16 126 (Polychromatic418967fa.accept_12_3_4_6_1_434 15
  16 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 16 126 2 7 8 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 16 126
  (Polychromatic418967fa.accept_19_13_16_12_1_6096 13 16 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 16 126 2 6 8 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 16 126 (accept_3_5 11 16 126 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 16 126 2 5 8 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 16 126 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 16 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 16 126 2 4 8 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 16 126 (Polychromatic418967fa.accept_13_7_3_9_1_1142 7 16 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 126 2 3 8 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 126 (accept_3_5 5 16 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 126 2 2 8 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 16 126 (Polychromatic418967fa.accept_12_3_4_6_1_434 3
  16 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 16 126 2 1 8 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 16 126
  (Polychromatic418967fa.accept_20_1_16_6_1_4715 1 16 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 16 126)))))))))))))))) (allB_succ 15 126 (allA_succ_of_accept 14 15 126
  (Polychromatic418967fa.accept_10_4_5_6_1_651 14 15 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 15 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 126 3 4 5 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 126 (Polychromatic418967fa.accept_10_1_5_6_1_649 11 15 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 126
  (Polychromatic418967fa.accept_11_10_4_5_1_359 10 15 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 15 126 3 3 5 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 15 126 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 15 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 126 (Polychromatic418967fa.accept_13_7_2_9_1_1826 7 15 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 15 126 3 2 5 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 15 126
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 15 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 15 126 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 15 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 126 3 1 5 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 126 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 15 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 126
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 15 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 15 126))))))))))))))) (allB_succ 14 126 (allA_succ_of_accept 13 14 126 (accept_3_4 13 14 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 126 2 6 7 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 126 (Polychromatic418967fa.accept_13_11_1_9_1_1179 11 14 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 14 126 2 5 7 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 14 126
  (Polychromatic418967fa.accept_12_9_2_6_1_455 9 14 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 14 126 2 4 7 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 14 126 7 1 2 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 14 126 2 3 7 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 14 126 (Polychromatic418967fa.accept_10_5_4_6_1_319 5 14 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 14 126 2 2 7 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 14 126 (Polychromatic418967fa.accept_12_3_2_6_1_138 3 14 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 126 2 1 7 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 126 (accept_3_4 1 14 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14 126)))))))))))))) (allB_succ 13 126 (allA_succ_of_accept 12 13
  126 (Polychromatic418967fa.accept_24_12_13_6_1_6095 12 13 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 13 126 (accept_3_5 11 13 126 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 13 126 (Polychromatic418967fa.accept_16_10_13_14_1_5042 10 13 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 13 126 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 13 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 126 (accept_3_5 8 13 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 13
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 126
  (Polychromatic418967fa.accept_17_6_13_7_1_272 6 13 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 126 (accept_3_5 5 13 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  126 (Polychromatic418967fa.accept_15_4_13_6_1_642 4 13 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 13 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 13 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 126 (accept_3_5 2 13 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 126 (Polychromatic418967fa.accept_16_1_13_14_1_1064 1 13 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 126))))))))))))) (allB_succ 12 126
  (allA_succ_of_accept 11 12 126 (Polychromatic418967fa.accept_10_1_2_6_1_638 11 12 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12 126 2 5 6 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 12 126 3 3 4 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 12 126 2 4 6 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 12 126 (Polychromatic418967fa.accept_15_7_12_6_1_1327 7 12 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 126 6 1 2 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 126
  (Polychromatic418967fa.accept_15_5_12_6_1_639 5 12 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 12 126 2 2 6 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 12 126 3 1 4 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 12 126 2 1 6 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 12 126 (Polychromatic418967fa.accept_10_1_2_6_1_638 1 12 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 12 126)))))))))))) (allB_succ 11 126 (allA_succ_of_accept 10 11 126
  (accept_3_4 10 11 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 126
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 11 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 126 (Polychromatic418967fa.accept_13_8_11_9_1_593 8 11 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 126 (accept_3_4 7 11 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 126 (Polychromatic418967fa.accept_22_6_11_16_1_6094 6 11 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 11
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 126 (accept_3_4 4 11 126
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 126 (Polychromatic418967fa.accept_15_3_11_6_1_3083
  3 11 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 126
  (Polychromatic418967fa.accept_10_2_1_6_1_634 2 11 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 126 (accept_3_4 1 11 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  126))))))))))) (allB_succ 10 126 (allA_succ_of_accept 9 10 126 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 10 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 10 126 2 4 5 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 10 126
  (Polychromatic418967fa.accept_16_7_10_14_1_1884 7 10 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 10 126 2 3 5 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 10 126 (accept_3_5 5 10 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 10 126
  2 2 5 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 10 126
  (Polychromatic418967fa.accept_12_3_10_6_1_442 3 10 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 10 126 2 1 5 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 10 126 (Polychromatic418967fa.accept_13_1_10_9_1_215 1 10 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 10 126)))))))))) (allB_succ 9 126 (allA_succ_of_accept 8 9 126
  (Polychromatic418967fa.accept_12_8_9_6_1_127 8 9 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 9 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 9 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 126 3 2 3 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 126 (Polychromatic418967fa.accept_10_5_9_6_1_697 5 9 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 126
  (Polychromatic418967fa.accept_12_4_9_6_1_440 4 9 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 9 126 3 1 3 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 9 126 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 9 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 126 (Polychromatic418967fa.accept_15_1_9_6_1_1323 1 9 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 126))))))))) (allB_succ 8 126
  (allA_succ_of_accept 7 8 126 (accept_3_4 7 8 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 8 126 2
  3 4 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 8 126
  (Polychromatic418967fa.accept_19_5_8_12_1_6093 5 8 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 8 126 2 2 4 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 8 126 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 8 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 126 2 1 4 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 126 (accept_3_4 1 8 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 8 126)))))))) (allB_succ 7 126 (allA_succ_of_accept 6 7 126
  (Polychromatic418967fa.accept_13_6_7_9_1_1848 6 7 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 126 (accept_3_5 5 7 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 126
  (Polychromatic418967fa.accept_13_4_7_9_1_5260 4 7 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 126 (Polychromatic418967fa.accept_10_3_7_6_1_659 3 7 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 126 (accept_3_5 2 7 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 7 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 126))))))) (allB_succ 6 126 (allA_succ_of_accept 5 6 126
  (Polychromatic418967fa.accept_23_5_6_11_1_6092 5 6 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 6 126 2 2 3 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 6 126 3 1 2 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 6 126 2 1 3 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 126 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1 6 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 6 126)))))) (allB_succ 5 126 (allA_succ_of_accept 4 5 126 (accept_3_4 4 5
  126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 126 (Polychromatic418967fa.accept_4_3_1_2_1_62 3
  5 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 126
  (Polychromatic418967fa.accept_13_2_5_9_1_610 2 5 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 126 (accept_3_4 1 5 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 126)))))
  (allB_succ 4 126 (allA_succ_of_accept 3 4 126 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 4 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 4 126 2 1 2 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 4 126 (Polychromatic418967fa.accept_16_1_4_14_1_1896 1
  4 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 4 126)))) (allB_succ 3 126
  (allA_succ_of_accept 2 3 126 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 3 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 126 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 3 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 126))) (allB_succ 2 126 (allA_succ_of_accept
  1 2 126 (accept_3_4 1 2 126 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 126)) (allB_two
  126))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


