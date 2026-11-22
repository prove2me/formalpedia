-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch130
-- name    : Polychromatic418967fa_Branch130
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:12:46.8114+00:00
-- url     : https://prove2.me/theorems/0d30e91a-1cc3-41d2-97d1-77ef5e0c7767
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

def Polychromatic418967fa.branch_130 : allB 130 130 :=
  allB_succ' 2 129 130 (Eq.refl Bool.true) (allA_succ_of_accept 1 129 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  129 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129 130)) (allB_succ' 3 128 130
  (Eq.refl Bool.true) (allA_of_3_1 3 128 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 127 130 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 127 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 127 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 127 130 (accept_3_3 2 127 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 127 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 127 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 127 130)))) (allB_succ' 5 126 130 (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 126 130 2 2 63 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 126 130 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 126 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 126 130 2 1 63 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 126 130 (Polychromatic418967fa.accept_15_1_6_10_1_23 1 126 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126 130))))) (allB_succ' 6 125 130 (Eq.refl
  Bool.true) (allA_of_3_1 6 125 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 124 130 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 124 130 2 3 62 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 124 130 (accept_3_3 5 124 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 124
  130 2 2 62 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  124 130 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 124 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 124 130 2 1 62 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 124 130 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 124 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 124 130))))))) (allB_succ' 8 123 130 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 123 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 123 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 130 (Polychromatic418967fa.accept_12_6_3_10_1_224 6 123 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 130 (accept_3_3 5 123 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 130 (Polychromatic418967fa.accept_11_4_2_9_1_496 4
  123 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 123 130
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 123 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 123 130 (accept_3_3 2 123 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  123 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 123 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 123 130)))))))) (allB_succ' 9 122 130 (Eq.refl Bool.true) (allA_of_3_1 9 122 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 121 130 (Eq.refl Bool.true) (allA_succ_of_accept 9 121 130
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 121 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 121 130 (accept_3_3 8 121 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  121 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 121 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 121 130 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 121 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 130 (accept_3_3 5 121 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 130 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 121 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 130
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 121 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 130 (accept_3_3 2 121 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 130 (Polychromatic418967fa.accept_16_1_9_2_1_4161 1 121 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121 130)))))))))) (allB_succ' 11 120 130 (Eq.refl Bool.true) (allA_succ_of_gcd 10 120 130 10 1
  12 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 120 130
  (Polychromatic418967fa.accept_18_9_12_4_1_1659 9 120 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 120 130 2 4 60 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 120 130 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 120 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120 130 2 3 60 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 120 130 5 1 24 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 120 130 2 2 60 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 120 130 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 120 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 120 130 2 1 60 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 130
  (Polychromatic418967fa.accept_9_1_3_4_1_47 1 120 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 120 130))))))))))) (allB_succ' 12 119 130 (Eq.refl Bool.true) (allA_of_3_1 12 119 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 13 118 130 (Eq.refl Bool.true) (allA_succ_of_gcd 12 118 130 2 6 59 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 118 130 (accept_3_3 11
  118 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 118 130 2 5 59 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 118 130
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 118 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 118 130 2 4 59 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 118 130 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 118 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 118 130 2 3 59 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 118 130 (accept_3_3 5 118 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 118 130 2 2 59 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 118 130 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 118 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 118 130 2 1 59 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 118 130 (Polychromatic418967fa.accept_15_1_13_10_1_1507
  1 118 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118 130))))))))))))) (allB_succ' 14
  117 130 (Eq.refl Bool.true) (allA_succ_of_gcd 13 117 130 13 1 9 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12 117 130 (Polychromatic418967fa.accept_18_12_9_4_1_2740 12 117
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 117 130 (accept_3_3 11 117
  130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 130
  (Polychromatic418967fa.accept_23_10_2_15_1_4798 10 117 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 117 130 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 117 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 130 (accept_3_3 8 117 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 117 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 130
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 117 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 117 130 (accept_3_3 5 117 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  117 130 (Polychromatic418967fa.accept_17_4_15_11_1_6465 4 117 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 117 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 117 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 130 (accept_3_3 2 117 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 117 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117 130)))))))))))))) (allB_succ' 15 116 130 (Eq.refl
  Bool.true) (allA_of_3_1 15 116 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 115 130 (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 115 130 5 3 23 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 115 130 (accept_3_3 14 115 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 115 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 115 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 115 130 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 115 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 115 130 (accept_3_3 11 115 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 115 130 5 2 23 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 115 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 115 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 115 130 (accept_3_3 8 115 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 115 130 (Polychromatic418967fa.accept_11_7_5_9_1_884 7
  115 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 130
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 115 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 115 130 5 1 23 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 115 130 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 115 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 115 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 115 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 130 (accept_3_3 2 115 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 1
  115 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115 130)))))))))))))))) (allB_succ' 17
  114 130 (Eq.refl Bool.true) (allA_succ_of_gcd 16 114 130 2 8 57 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 114 130 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 114
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 114 130 2 7 57 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 114 130
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 114 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 114 130 2 6 57 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 114 130 (accept_3_3 11 114 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  114 130 2 5 57 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 114 130 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 114 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 114 130 2 4 57 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 114 130 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 114 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114 130 2 3 57 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 114 130 (accept_3_3 5 114 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 114 130 2 2 57 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 114 130 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 114 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 114 130 2 1 57 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 130
  (Polychromatic418967fa.accept_9_1_6_4_1_49 1 114 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 114 130))))))))))))))))) (allB_succ' 18 113 130 (Eq.refl Bool.true) (allA_of_3_1 18 113 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 112 130 (Eq.refl Bool.true) (allA_succ_of_gcd 18 112 130 2 9 56 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 112 130
  (accept_3_3 17 112 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 112 130 2 8 56 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 112 130
  (Polychromatic418967fa.accept_11_4_2_9_1_496 15 112 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 112 130 2 7 56 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 112 130 (Polychromatic418967fa.accept_12_1_4_10_1_209 13 112 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 112 130 2 6 56 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 112 130 (accept_3_3 11 112 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 112 130 2 5 56 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 112 130 (Polychromatic418967fa.accept_25_9_12_5_1_6535 9 112 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 112 130 2 4 56 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 112 130
  (Polychromatic418967fa.accept_11_7_2_9_1_480 7 112 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 112 130 2 3 56 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 112 130 (accept_3_3 5 112 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 112
  130 2 2 56 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  112 130 (Polychromatic418967fa.accept_15_3_7_10_1_2324 3 112 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 112 130 2 1 56 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 112 130 (Polychromatic418967fa.accept_12_1_4_10_1_209 1 112 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112 130))))))))))))))))))) (allB_succ' 20 111 130 (Eq.refl
  Bool.true) (allA_succ_of_accept 19 111 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 111 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 130 (Polychromatic418967fa.accept_12_6_3_10_1_224
  18 111 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 130 (accept_3_3 17
  111 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 130
  (Polychromatic418967fa.accept_7_2_6_4_1_29 16 111 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 111 130 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 111 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 130 (accept_3_3 14 111 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 111 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 111 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 130 (Polychromatic418967fa.accept_7_5_6_4_1_117
  12 111 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 130 (accept_3_3 11
  111 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 130
  (Polychromatic418967fa.accept_7_3_6_4_1_30 10 111 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 111 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 111 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 130 (accept_3_3 8 111 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 111 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 111 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 130 (Polychromatic418967fa.accept_9_6_3_4_1_477 6
  111 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 130 (accept_3_3 5 111
  130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 130
  (Polychromatic418967fa.accept_15_4_6_10_1_823 4 111 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 111 130 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 111 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 130 (accept_3_3 2 111 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 111 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 111 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111 130)))))))))))))))))))) (allB_succ' 21 110 130 (Eq.refl
  Bool.true) (allA_of_3_1 21 110 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 109 130 (Eq.refl Bool.true)
  (allA_succ_of_accept 21 109 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 109 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 109 130 (accept_3_3 20 109 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 109 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 109 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 109 130
  (Polychromatic418967fa.accept_17_1_7_11_1_2892 18 109 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 109 130 (accept_3_3 17 109 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 109 130 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 109 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 109 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 109 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 109 130 (accept_3_3 14 109 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 109 130 (Polychromatic418967fa.accept_15_13_4_10_1_821 13 109 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 109 130
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 109 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 109 130 (accept_3_3 11 109 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 109 130 (Polychromatic418967fa.accept_22_10_21_20_1_6534 10 109 130 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 109 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 109 130 (accept_3_3 8 109 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 109 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 109 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 109 130
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 109 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 109 130 (accept_3_3 5 109 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  109 130 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 109 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 109 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 109 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 109 130 (accept_3_3 2 109 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 109 130 (Polychromatic418967fa.accept_11_1_10_9_1_871 1 109 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 109 130)))))))))))))))))))))) (allB_succ' 23 108 130
  (Eq.refl Bool.true) (allA_succ_of_gcd 22 108 130 2 11 54 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 108 130 (Polychromatic418967fa.accept_14_7_10_4_1_130 21 108
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 108 130 2 10 54 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 108 130
  (Polychromatic418967fa.accept_23_19_16_15_1_6533 19 108 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 108 130 2 9 54 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 108 130 (accept_3_3 17 108 130 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 108 130 2 8 54 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 108 130 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 108 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 108 130 2 7 54 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 108 130 (Polychromatic418967fa.accept_7_6_3_4_1_294 13
  108 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 130 2 6 54 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 130 (accept_3_3 11
  108 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 108 130 2 5 54 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 108 130
  (Polychromatic418967fa.accept_15_9_3_10_1_2312 9 108 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 108 130 2 4 54 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 108 130 (Polychromatic418967fa.accept_14_7_10_4_1_130 7 108 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 130 2 3 54 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 130 (accept_3_3 5 108 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 108 130 2 2 54 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 108 130 (Polychromatic418967fa.accept_19_3_13_16_1_6532 3 108 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 108 130 2 1 54 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 108 130
  (Polychromatic418967fa.accept_7_1_3_4_1_128 1 108 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 108 130))))))))))))))))))))))) (allB_succ' 24 107 130 (Eq.refl Bool.true) (allA_of_3_1 24 107 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 106 130 (Eq.refl Bool.true) (allA_succ_of_gcd 24 106 130 2 12 53 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 106 130
  (accept_3_3 23 106 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 106 130 2 11 53 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 106 130
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 106 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 106 130 2 10 53 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 106 130 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 106 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 106 130 2 9 53 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 106 130 (accept_3_3 17 106 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 106 130 2 8 53 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 106 130 (Polychromatic418967fa.accept_9_6_7_4_1_212 15
  106 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 106 130 2 7 53 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 106 130
  (Polychromatic418967fa.accept_11_2_7_9_1_890 13 106 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 106 130 2 6 53 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 106 130 (accept_3_3 11 106 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  106 130 2 5 53 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 106 130 (Polychromatic418967fa.accept_15_9_1_10_1_4316 9 106 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 106 130 2 4 53 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 106 130 (Polychromatic418967fa.accept_15_7_1_10_1_305 7 106 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 106 130 2 3 53 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 106 130 (accept_3_3 5 106 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 106 130 2 2 53 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 106 130 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 106 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 106 130 2 1 53 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 106 130
  (Polychromatic418967fa.accept_9_1_7_4_1_52 1 106 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 106 130))))))))))))))))))))))))) (allB_succ' 26 105 130 (Eq.refl Bool.true) (allA_succ_of_gcd 25 105 130 5 5
  21 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 105 130
  (Polychromatic418967fa.accept_14_10_7_4_1_3453 24 105 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 105 130 (accept_3_3 23 105 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 105 130 (Polychromatic418967fa.accept_16_6_9_2_1_6518 22 105 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 105 130 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 105 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 105 130 5 4 21 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 105 130
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 105 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 105 130 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 105 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 130 (accept_3_3 17 105 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 105 130 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 105 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 105 130 5 3 21 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 105 130 (accept_3_3 14 105 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 105 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 130
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 105 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 105 130 (accept_3_3 11 105 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  105 130 5 2 21 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 105 130 (Polychromatic418967fa.accept_17_9_3_11_1_3983 9 105 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 105 130 (accept_3_3 8 105 130 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 105 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 105 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 130 (Polychromatic418967fa.accept_12_6_9_10_1_565 6 105 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 105 130 5 1 21 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 105 130
  (Polychromatic418967fa.accept_19_4_10_16_1_6531 4 105 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 105 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 105 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 130 (accept_3_3 2 105 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 105 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 105 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105 130)))))))))))))))))))))))))) (allB_succ' 27 104 130 (Eq.refl
  Bool.true) (allA_of_3_1 27 104 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 103 130 (Eq.refl Bool.true)
  (allA_succ_of_accept 27 103 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 103 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 103 130 (accept_3_3 26 103 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 103 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 103 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 103 130 (Polychromatic418967fa.accept_11_2_4_9_1_484
  24 103 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 130 (accept_3_3 23
  103 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 130
  (Polychromatic418967fa.accept_7_1_5_4_1_134 22 103 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 103 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 103 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 103 130 (accept_3_3 20 103 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 103 130 (Polychromatic418967fa.accept_15_4_13_10_1_1508 19 103 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 103 130
  (Polychromatic418967fa.accept_15_3_13_10_1_2332 18 103 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 103 130 (accept_3_3 17 103 130 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 103 130 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 103 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 103 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 103 130 (accept_3_3 14 103 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 103 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 13
  103 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 103 130
  (Polychromatic418967fa.accept_15_12_13_10_1_812 12 103 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 103 130 (accept_3_3 11 103 130 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 103 130 (Polychromatic418967fa.accept_17_10_1_11_1_2900 10 103 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 9
  103 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 103 130 (accept_3_3 8 103
  130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 103 130
  (Polychromatic418967fa.accept_17_7_1_11_1_1894 7 103 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 103 130 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 103 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 130 (accept_3_3 5 103 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 103 130 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 103 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 3
  103 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 103 130 (accept_3_3 2 103
  130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 103 130 (Polychromatic418967fa.accept_4_1_3_2_1_3
  1 103 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 103 130))))))))))))))))))))))))))))
  (allB_succ' 29 102 130 (Eq.refl Bool.true) (allA_succ_of_gcd 28 102 130 2 14 51 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 102 130
  (Polychromatic418967fa.accept_12_3_6_10_1_576 27 102 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 102 130 2 13 51 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 102 130 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 102 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 102 130 2 12 51 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 102 130 (accept_3_3 23 102 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 102 130 2 11 51 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 102 130 (Polychromatic418967fa.accept_12_9_6_10_1_1085
  21 102 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 102 130 2 10 51 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 102 130
  (Polychromatic418967fa.accept_9_1_3_4_1_47 19 102 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 130 2 9 51 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 130 (accept_3_3 17 102 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  102 130 2 8 51 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 102 130 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 102 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 102 130 2 7 51 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 102 130 (Polychromatic418967fa.accept_15_13_12_10_1_4352 13 102 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 130 2 6 51 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 130 (accept_3_3 11
  102 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 102 130 2 5 51 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 102 130
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 102 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 102 130 2 4 51 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 102 130 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 102 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102 130 2 3 51 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 102 130 (accept_3_3 5 102 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 102 130 2 2 51 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 102 130 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 102 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 102 130 2 1 51 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 130 (Polychromatic418967fa.accept_9_1_3_4_1_47 1
  102 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102 130)))))))))))))))))))))))))))))
  (allB_succ' 30 101 130 (Eq.refl Bool.true) (allA_of_3_1 30 101 130 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 31 100 130 (Eq.refl Bool.true) (allA_succ_of_gcd 30 100 130 10 3 10 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 100 130 (accept_3_3 29 100 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 100 130 2 14 50 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 100 130 (Polychromatic418967fa.accept_7_6_2_4_1_291 27
  100 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 100 130 2 13 50 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 100 130 5 5 20 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 100 130 2 12 50 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 100 130
  (accept_3_3 23 100 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 100 130 2 11 50 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 100 130
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 100 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 100 130 10 2 10 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 100 130 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 100 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 100 130 2 9 50 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 100 130 (accept_3_3 17 100 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 100 130 2 8 50 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 100 130 5 3 20 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 100 130 2 7 50 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 100 130 (Polychromatic418967fa.accept_7_6_2_4_1_291 13
  100 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 100 130 2 6 50 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 100 130 (accept_3_3 11
  100 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 100 130 10 1 10 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 100 130
  (Polychromatic418967fa.accept_14_9_2_4_1_1814 9 100 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 100 130 2 4 50 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 100 130 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 100 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 100 130 2 3 50 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 100 130 5 1 20 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 100 130 2 2 50 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 100 130 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 100 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 100 130 2 1 50 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 100 130
  (Polychromatic418967fa.accept_12_1_4_10_1_209 1 100 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 100 130))))))))))))))))))))))))))))))) (allB_succ' 32 99 130 (Eq.refl Bool.true) (allA_succ_of_accept 31 99
  130 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 99 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 99 130 (Polychromatic418967fa.accept_12_6_3_10_1_224 30 99 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 130 (accept_3_3 29 99 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 99 130 (Polychromatic418967fa.accept_19_9_4_16_1_2586 28 99 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 130
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 27 99 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 99 130 (accept_3_3 26 99 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  99 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 99 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 99 130 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 99 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 130 (accept_3_3 23 99 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 130 (Polychromatic418967fa.accept_16_6_3_2_1_3096 22 99 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 130
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 99 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 99 130 (accept_3_3 20 99 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  99 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 99 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 99 130 (Polychromatic418967fa.accept_12_6_3_10_1_224 18 99 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 130 (accept_3_3 17 99 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 130 (Polychromatic418967fa.accept_15_1_9_10_1_2327 16 99 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 130
  (Polychromatic418967fa.accept_16_15_3_2_1_4170 15 99 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 99 130 (accept_3_3 14 99 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  99 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 99 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 99 130 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 99 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 130 (accept_3_3 11 99 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 130 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 99 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 130
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 99 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 99 130 (accept_3_3 8 99 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99
  130 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 99 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 99 130 (Polychromatic418967fa.accept_12_6_3_10_1_224 6 99 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 130 (accept_3_3 5 99 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 99 130 (Polychromatic418967fa.accept_15_4_9_10_1_5384 4 99 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 130 (Polychromatic418967fa.accept_7_3_1_4_1_121 3
  99 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 130 (accept_3_3 2 99 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 99
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99 130))))))))))))))))))))))))))))))))
  (allB_succ' 33 98 130 (Eq.refl Bool.true) (allA_of_3_1 33 98 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  34 97 130 (Eq.refl Bool.true) (allA_succ_of_accept 33 97 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 97 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 130 (accept_3_3 32 97 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 97 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 31
  97 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 130
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 97 130 (accept_3_3 29 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  97 130 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 97 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 97 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 130 (accept_3_3 26 97 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 130 (Polychromatic418967fa.accept_16_9_1_2_1_2126 25 97 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 130
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 130 (accept_3_3 23 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 130 (Polychromatic418967fa.accept_16_6_1_2_1_3129 22 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 97 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 130 (accept_3_3 20 97 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 97 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 130
  (Polychromatic418967fa.accept_15_3_7_10_1_2324 18 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 130 (accept_3_3 17 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 130 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 97 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 130 (accept_3_3 14 97 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 130 (Polychromatic418967fa.accept_17_13_12_11_1_2947 13 97 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 130
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 130 (accept_3_3 11 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 130 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 97 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 130 (accept_3_3 8 97 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 97 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 130
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 130 (accept_3_3 5 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  130 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 97 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 97 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 97 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 130 (accept_3_3 2 97 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 97 130 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 97 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97 130)))))))))))))))))))))))))))))))))) (allB_succ' 35
  96 130 (Eq.refl Bool.true) (allA_succ_of_gcd 34 96 130 2 17 48 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 96 130 (Polychromatic418967fa.accept_15_3_6_10_1_1539 33 96 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 96 130 2 16 48 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 96 130
  (Polychromatic418967fa.accept_15_1_6_10_1_23 31 96 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 96 130 2 15 48 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 96 130 (accept_3_3 29 96 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 96
  130 2 14 48 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  96 130 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 96 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 96 130 2 13 48 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 96 130 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 96 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96 130 2 12 48 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 96 130 (accept_3_3 23 96 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 96 130 2 11 48 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 96 130
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 96 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 96 130 2 10 48 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 96 130 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 96 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 130 2 9 48 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 130 (accept_3_3 17 96 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 96 130 2 8 48 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 96 130 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 96 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 96 130 2 7 48 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 96 130 (Polychromatic418967fa.accept_7_6_5_4_1_297 13
  96 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 130 2 6 48 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 130 (accept_3_3 11
  96 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96 130 2 5 48 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 96 130
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 96 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 96 130 2 4 48 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 96 130 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 96 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 130 2 3 48 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 130 (accept_3_3 5 96 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 96 130 2 2 48 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 96 130 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 96 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 96 130 2 1 48 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 130 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 96
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96 130)))))))))))))))))))))))))))))))))))
  (allB_succ' 36 95 130 (Eq.refl Bool.true) (allA_of_3_1 36 95 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  37 94 130 (Eq.refl Bool.true) (allA_succ_of_gcd 36 94 130 2 18 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 94 130 (accept_3_3 35 94 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 94 130 2 17 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 94 130 (Polychromatic418967fa.accept_19_14_18_16_1_6530 33 94 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 94 130 2 16 47 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 94 130
  (Polychromatic418967fa.accept_20_11_14_10_1_2320 31 94 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 94 130 2 15 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 94 130 (accept_3_3 29 94 130 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 94 130 2 14 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 94 130 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 94 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 94 130 2 13 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 94 130 (Polychromatic418967fa.accept_11_3_6_9_1_1378
  25 94 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 94 130 2 12 47 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 94 130 (accept_3_3 23
  94 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 94 130 2 11 47 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 94 130
  (Polychromatic418967fa.accept_14_7_10_4_1_130 21 94 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 94 130 2 10 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 94 130 (Polychromatic418967fa.accept_17_2_9_11_1_4057 19 94 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 94 130 2 9 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 94 130 (accept_3_3 17 94 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 94 130 2 8 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 94 130 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 94 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 94 130 2 7 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 94 130 (Polychromatic418967fa.accept_7_6_3_4_1_294 13
  94 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 94 130 2 6 47 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 94 130 (accept_3_3 11
  94 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 94 130 2 5 47 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 94 130
  (Polychromatic418967fa.accept_15_9_4_10_1_2316 9 94 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 94 130 2 4 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 94 130 (Polychromatic418967fa.accept_14_7_10_4_1_130 7 94 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 94 130 2 3 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 94 130 (accept_3_3 5 94 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 94 130 2 2 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 94 130 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 94 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 94 130 2 1 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 94 130 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 94
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94 130)))))))))))))))))))))))))))))))))))))
  (allB_succ' 38 93 130 (Eq.refl Bool.true) (allA_succ_of_accept 37 93 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 37
  93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 93 130
  (Polychromatic418967fa.accept_15_6_3_10_1_2341 36 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 93 130 (accept_3_3 35 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  93 130 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 93 130 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 93 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 130 (accept_3_3 32 93 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 93 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 93 130
  (Polychromatic418967fa.accept_12_6_9_10_1_565 30 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 93 130 (accept_3_3 29 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  93 130 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 93 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 93 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 130 (accept_3_3 26 93 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 93 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 93 130
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 93 130 (accept_3_3 23 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  93 130 (Polychromatic418967fa.accept_15_7_3_10_1_817 22 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 93 130 (Polychromatic418967fa.accept_15_6_3_10_1_2341 21 93 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 130 (accept_3_3 20 93 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 93 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 93 130
  (Polychromatic418967fa.accept_11_7_5_9_1_884 18 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 93 130 (accept_3_3 17 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  93 130 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 93 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 93 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 130 (accept_3_3 14 93 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 93 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 93 130
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 93 130 (accept_3_3 11 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  93 130 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 93 130 (Polychromatic418967fa.accept_15_9_3_10_1_2312 9 93 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 130 (accept_3_3 8 93 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 93 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93 130
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 130 (accept_3_3 5 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93
  130 (Polychromatic418967fa.accept_25_4_18_5_1_6529 4 93 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 93 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 130 (accept_3_3 2 93 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 93 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93 130)))))))))))))))))))))))))))))))))))))) (allB_succ'
  39 92 130 (Eq.refl Bool.true) (allA_of_3_1 39 92 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 40 91 130
  (Eq.refl Bool.true) (allA_succ_of_gcd 39 91 130 13 3 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 38 91 130 (accept_3_3 38 91 130 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 91 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 91 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 91 130 (Polychromatic418967fa.accept_15_6_1_10_1_1549 36 91
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 91 130 (accept_3_3 35 91 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 91 130 (Polychromatic418967fa.accept_9_7_1_4_1_217 34
  91 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 91 130
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 91 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 91 130 (accept_3_3 32 91 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  91 130 (Polychromatic418967fa.accept_14_3_7_4_1_118 31 91 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 91 130 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 91 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 91 130 (accept_3_3 29 91 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 91 130 (Polychromatic418967fa.accept_11_6_3_9_1_906 28 91 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 91 130
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 91 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 91 130 13 2 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 91 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 91 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 130 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 91 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 130 (accept_3_3 23 91 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 130 (Polychromatic418967fa.accept_15_7_1_10_1_305
  22 91 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 91 130
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 91 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 91 130 (accept_3_3 20 91 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  91 130 (Polychromatic418967fa.accept_20_19_11_10_1_3615 19 91 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 91 130 (Polychromatic418967fa.accept_19_18_15_16_1_6528 18 91 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 130 (accept_3_3 17 91 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 130 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 91 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 130
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 91 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 91 130 (accept_3_3 14 91 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 91
  130 13 1 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12
  91 130 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 91 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 91 130 (accept_3_3 11 91 130 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 91 130 (Polychromatic418967fa.accept_14_10_7_4_1_3453 10 91 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 91 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 130 (accept_3_3 8 91 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 130 (Polychromatic418967fa.accept_9_7_1_4_1_217 7
  91 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 130
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 91 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 130 (accept_3_3 5 91 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  130 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 91 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 91 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 91 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 130 (accept_3_3 2 91 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 91 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91 130))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 41 90 130 (Eq.refl Bool.true) (allA_succ_of_gcd 40 90 130 10 4 9 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 90 130
  (Polychromatic418967fa.accept_12_3_6_10_1_576 39 90 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 90 130 2 19 45 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 90 130 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 90 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 90 130 2 18 45 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 90 130 5 7 18 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 90 130 2 17 45 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 90 130 (Polychromatic418967fa.accept_7_5_6_4_1_117 33
  90 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 90 130 2 16 45 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 90 130
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 90 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 90 130 10 3 9 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 90 130 (accept_3_3 29 90 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 90
  130 2 14 45 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  90 130 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 90 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 90 130 2 13 45 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 25 90 130 5 5 18 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 90 130 2 12 45 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 90 130 (accept_3_3 23 90 130 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 90 130 2 11 45 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 90 130 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 90 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 90 130 10 2 9 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 130 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 90 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90 130 2 9 45 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 90 130 (accept_3_3 17 90 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 130 2 8 45 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 90 130 5 3 18 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 90 130 2 7 45 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 130
  (Polychromatic418967fa.accept_19_13_14_16_1_6527 13 90 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 90 130 2 6 45 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 90 130 (accept_3_3 11 90 130 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 90 130 10 1 9 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 90 130 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 90 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 90 130 2 4 45 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 130 (Polychromatic418967fa.accept_11_7_2_9_1_480 7 90 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 130 2 3 45 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 90 130 5 1 18 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 90 130 2 2 45 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 90 130
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 90 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 90 130 2 1 45 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 90 130 (Polychromatic418967fa.accept_25_1_15_5_1_6526 1 90 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 90 130))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 89 130
  (Eq.refl Bool.true) (allA_of_3_1 42 89 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 88 130 (Eq.refl
  Bool.true) (allA_succ_of_gcd 42 88 130 2 21 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 88 130 (accept_3_3 41 88 130 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 88 130 2 20 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 88 130 (Polychromatic418967fa.accept_9_3_7_4_1_53 39 88 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 88 130 2 19 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 88 130 (Polychromatic418967fa.accept_9_1_7_4_1_52 37
  88 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 88 130 2 18 44 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 88 130 (accept_3_3 35
  88 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 88 130 2 17 44 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 88 130
  (Polychromatic418967fa.accept_9_6_7_4_1_212 33 88 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 88 130 2 16 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 88 130 (Polychromatic418967fa.accept_12_7_4_10_1_572 31 88 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 88 130 2 15 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 88 130 (accept_3_3 29 88 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 88 130 2 14 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 88 130 (Polychromatic418967fa.accept_15_12_13_10_1_812 27 88
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 88 130 2 13 44 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 88 130
  (Polychromatic418967fa.accept_12_1_4_10_1_209 25 88 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 88 130 2 12 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 88 130 (accept_3_3 23 88 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 88
  130 2 11 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  88 130 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 88 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 88 130 2 10 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 88 130 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 88 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 88 130 2 9 44 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 88 130 (accept_3_3 17 88 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 88 130 2 8 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 88 130 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 88 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 88 130 2 7 44 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 88 130
  (Polychromatic418967fa.accept_12_1_4_10_1_209 13 88 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 88 130 2 6 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 88 130 (accept_3_3 11 88 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 88
  130 2 5 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  88 130 (Polychromatic418967fa.accept_17_9_3_11_1_3983 9 88 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 88 130 2 4 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 88 130 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 88 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 88 130 2 3 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 88 130 (accept_3_3 5 88 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 88 130 2 2 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 88 130 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 88 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 88 130 2 1 44 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 88 130
  (Polychromatic418967fa.accept_9_1_7_4_1_52 1 88 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 88 130))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 87 130 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 87 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 87 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 87 130 (Polychromatic418967fa.accept_12_6_3_10_1_224 42 87 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 130 (accept_3_3 41 87 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 130
  (Polychromatic418967fa.accept_19_2_11_16_1_6525 40 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 87 130 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 87 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 130 (accept_3_3 38 87 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 87 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 87 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 87 130 (Polychromatic418967fa.accept_7_1_3_4_1_128 36
  87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 130 (accept_3_3 35 87
  130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 130
  (Polychromatic418967fa.accept_7_6_3_4_1_294 34 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 87 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 87 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 130 (accept_3_3 32 87 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 87 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 87 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 87 130 (Polychromatic418967fa.accept_9_3_6_4_1_210 30
  87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 130 (accept_3_3 29 87
  130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 130 (Polychromatic418967fa.accept_9_1_6_4_1_49
  28 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 130
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 87 130 (accept_3_3 26 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  87 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 87 130 (Polychromatic418967fa.accept_15_9_12_10_1_809 24 87 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 130 (accept_3_3 23 87 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 130 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 87 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 130
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 87 130 (accept_3_3 20 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  87 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 87 130 (Polychromatic418967fa.accept_12_6_3_10_1_224 18 87 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 130 (accept_3_3 17 87 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 130 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 87 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 130
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 87 130 (accept_3_3 14 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  87 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 87 130 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 87 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 130 (accept_3_3 11 87 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 130 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 87 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 130
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 130 (accept_3_3 8 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87
  130 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 87 130 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 87 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 130 (accept_3_3 5 87 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 87 130 (Polychromatic418967fa.accept_19_4_11_16_1_1474 4 87 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 130 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  87 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 130 (accept_3_3 2 87 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 87
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  130)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 86 130 (Eq.refl Bool.true) (allA_of_3_1 45 86 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 46 85 130 (Eq.refl Bool.true) (allA_succ_of_gcd 45 85 130 5 9 17
  26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 85 130
  (accept_3_3 44 85 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 130
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 85 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 85 130 (Polychromatic418967fa.accept_19_4_9_16_1_3811 42 85 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 85 130 (accept_3_3 41 85 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 85 130 5 8 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 85 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 85 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 130 (accept_3_3 38 85 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 130 (Polychromatic418967fa.accept_19_18_9_16_1_6524 37 85 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 130
  (Polychromatic418967fa.accept_20_16_5_10_1_6487 36 85 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 85 130 5 7 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 85 130 (Polychromatic418967fa.accept_20_14_5_10_1_3647 34 85 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 85 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 85 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 130 (accept_3_3 32 85 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 31
  85 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 85 130 5 6 17 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 85 130 (accept_3_3 29
  85 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 85 130
  (Polychromatic418967fa.accept_12_4_1_10_1_221 28 85 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 85 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 85 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 130 (accept_3_3 26 85 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 85 130 5 5 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 24 85 130 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 85 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 85 130 (accept_3_3 23 85 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 85 130 (Polychromatic418967fa.accept_20_2_5_10_1_3535 22 85 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 85 130
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 85 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 85 130 5 4 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 85 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 85 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 130 (Polychromatic418967fa.accept_19_18_9_16_1_6524 18 85
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 130 (accept_3_3 17 85 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 85 130 (Polychromatic418967fa.accept_12_4_1_10_1_221
  16 85 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 85 130 5 3 17 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 85 130 (accept_3_3 14
  85 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 130
  (Polychromatic418967fa.accept_16_13_5_2_1_2131 13 85 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 85 130 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 85 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 85 130 (accept_3_3 11 85 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 85 130 5 2 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 85 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 85 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 130 (accept_3_3 8 85 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 85 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 130
  (Polychromatic418967fa.accept_19_6_9_16_1_1468 6 85 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 85 130 5 1 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 85 130 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 85 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 85 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 85 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 130 (accept_3_3 2 85 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 130 (Polychromatic418967fa.accept_20_1_5_10_1_3534
  1 85 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  130)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 84 130 (Eq.refl Bool.true) (allA_succ_of_gcd 46 84
  130 2 23 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  84 130 (Polychromatic418967fa.accept_18_9_12_4_1_1659 45 84 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 84 130 2 22 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 84 130 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 84 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 130 2 21 42 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 130 (accept_3_3 41 84 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 84 130 2 20 42 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 84 130
  (Polychromatic418967fa.accept_17_5_16_11_1_3998 39 84 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 84 130 2 19 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 84 130 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 84 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84 130 2 18 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 84 130 (accept_3_3 35 84 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 84 130 2 17 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 84 130 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 84 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 84 130 2 16 42 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 84 130
  (Polychromatic418967fa.accept_15_1_9_10_1_2327 31 84 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 84 130 2 15 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 84 130 (accept_3_3 29 84 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 84
  130 2 14 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  84 130 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 84 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 84 130 2 13 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 84 130 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 84 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 130 2 12 42 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 130 (accept_3_3 23 84 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84 130 2 11 42 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 84 130
  (Polychromatic418967fa.accept_20_1_4_10_1_3645 21 84 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 84 130 2 10 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 84 130 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 84 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 130 2 9 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 130 (accept_3_3 17 84 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 84 130 2 8 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 84 130 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 84 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 130 2 7 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 130 (Polychromatic418967fa.accept_11_2_7_9_1_890 13
  84 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 130 2 6 42 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 130 (accept_3_3 11
  84 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 130 2 5 42 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 84 130
  (Polychromatic418967fa.accept_18_9_12_4_1_1659 9 84 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 84 130 2 4 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 84 130 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 84 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 130 2 3 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 130 (accept_3_3 5 84 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 84 130 2 2 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 84 130 (Polychromatic418967fa.accept_15_3_9_10_1_2325 3 84 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 84 130 2 1 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 130 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 84
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  130))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 83 130 (Eq.refl Bool.true) (allA_of_3_1 48 83 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 82 130 (Eq.refl Bool.true) (allA_succ_of_gcd 48 82 130 2 24 41
  65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 82 130
  (accept_3_3 47 82 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 82 130 2 23 41 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 82 130
  (Polychromatic418967fa.accept_19_7_6_16_1_3818 45 82 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 82 130 2 22 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 82 130 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 82 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 82 130 2 21 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 82 130 (accept_3_3 41 82 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 82 130 2 20 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 82 130 (Polychromatic418967fa.accept_9_3_1_4_1_216 39 82 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 82 130 2 19 41 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 82 130
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 82 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 82 130 2 18 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 82 130 (accept_3_3 35 82 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 82
  130 2 17 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  82 130 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 82 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 82 130 2 16 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 82 130 (Polychromatic418967fa.accept_15_1_7_10_1_287 31 82 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 82 130 2 15 41 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 82 130 (accept_3_3 29 82 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 82 130 2 14 41 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 82 130
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 82 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 82 130 2 13 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 82 130 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 82 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 82 130 2 12 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 82 130 (accept_3_3 23 82 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 82 130 2 11 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 82 130 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 82 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 82 130 2 10 41 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 82 130
  (Polychromatic418967fa.accept_15_4_7_10_1_807 19 82 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 82 130 2 9 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 82 130 (accept_3_3 17 82 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 82
  130 2 8 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  82 130 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 82 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 82 130 2 7 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 82 130 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 82 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 82 130 2 6 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 82 130 (accept_3_3 11 82 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 82 130 2 5 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 82 130 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 82 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 82 130 2 4 41 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 82 130
  (Polychromatic418967fa.accept_9_7_1_4_1_217 7 82 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 82 130 2 3 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 82 130 (accept_3_3 5 82 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 82 130
  2 2 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 82
  130 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 82 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 82 130 2 1 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 82 130 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 82 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 82 130))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 81
  130 (Eq.refl Bool.true) (allA_succ_of_accept 49 81 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 81 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 81 130
  (Polychromatic418967fa.accept_15_3_6_10_1_1539 48 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 81 130 (accept_3_3 47 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  81 130 (Polychromatic418967fa.accept_11_2_4_9_1_484 46 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 81 130 (Polychromatic418967fa.accept_20_5_1_10_1_6523 45 81 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 81 130 (accept_3_3 44 81 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 81 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 81 130
  (Polychromatic418967fa.accept_12_6_9_10_1_565 42 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 81 130 (accept_3_3 41 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  81 130 (Polychromatic418967fa.accept_17_6_13_11_1_995 40 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 81 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 81 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 81 130 (accept_3_3 38 81 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 81 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 81 130
  (Polychromatic418967fa.accept_14_8_11_4_1_3438 36 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 81 130 (accept_3_3 35 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  81 130 (Polychromatic418967fa.accept_15_4_6_10_1_823 34 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 81 130 (Polychromatic418967fa.accept_15_3_6_10_1_1539 33 81 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 81 130 (accept_3_3 32 81 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 81 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 81 130
  (Polychromatic418967fa.accept_12_6_9_10_1_565 30 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 81 130 (accept_3_3 29 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  81 130 (Polychromatic418967fa.accept_16_12_1_2_1_2163 28 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 81 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 81 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 81 130 (accept_3_3 26 81 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 81 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 130
  (Polychromatic418967fa.accept_11_2_4_9_1_484 24 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 81 130 (accept_3_3 23 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  81 130 (Polychromatic418967fa.accept_14_8_11_4_1_3438 22 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 81 130 (Polychromatic418967fa.accept_14_7_11_4_1_3455 21 81 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 81 130 (accept_3_3 20 81 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 81 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 130
  (Polychromatic418967fa.accept_12_6_9_10_1_565 18 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 81 130 (accept_3_3 17 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  81 130 (Polychromatic418967fa.accept_15_1_6_10_1_23 16 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 81 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 81 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 81 130 (accept_3_3 14 81 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 81 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 130
  (Polychromatic418967fa.accept_15_12_6_10_1_1516 12 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 81 130 (accept_3_3 11 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  81 130 (Polychromatic418967fa.accept_19_10_5_16_1_6522 10 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 81 130 (Polychromatic418967fa.accept_16_9_1_2_1_2126 9 81 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 81 130 (accept_3_3 8 81 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 81 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 130
  (Polychromatic418967fa.accept_12_6_9_10_1_565 6 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 81 130 (accept_3_3 5 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81
  130 (Polychromatic418967fa.accept_15_4_6_10_1_823 4 81 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 81 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 81 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 130 (accept_3_3 2 81 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 81 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81 130))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 51 80 130 (Eq.refl Bool.true) (allA_of_3_1 51 80 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  52 79 130 (Eq.refl Bool.true) (allA_succ_of_accept 51 79 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 79 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 130 (accept_3_3 50 79 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 49
  79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 79 130
  (Polychromatic418967fa.accept_7_6_2_4_1_291 48 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 79 130 (accept_3_3 47 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  79 130 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 79 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 79 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 130 (accept_3_3 44 79 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 130 (Polychromatic418967fa.accept_15_13_4_10_1_821 43 79 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 130
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 79 130 (accept_3_3 41 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  79 130 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 79 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 79 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 130 (accept_3_3 38 79 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 79 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 130
  (Polychromatic418967fa.accept_15_6_4_10_1_2319 36 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 130 (accept_3_3 35 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 130 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 79 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 130 (accept_3_3 32 79 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 130 (Polychromatic418967fa.accept_18_13_7_4_1_2738 31 79 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 130
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 130 (accept_3_3 29 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 130 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 79 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 130 (accept_3_3 26 79 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 79 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 130
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 130 (accept_3_3 23 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 130 (Polychromatic418967fa.accept_15_7_4_10_1_1513 22 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 79 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 130 (accept_3_3 20 79 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 130 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 79 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 130
  (Polychromatic418967fa.accept_11_7_2_9_1_480 18 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 130 (accept_3_3 17 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 130 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 79 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 130 (accept_3_3 14 79 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 79 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 130
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 130 (accept_3_3 11 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 130 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 79 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 130 (accept_3_3 8 79 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 130 (Polychromatic418967fa.accept_11_7_2_9_1_480 7 79 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 130
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 130 (accept_3_3 5 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  130 (Polychromatic418967fa.accept_11_4_2_9_1_496 4 79 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 79 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 79 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 130 (accept_3_3 2 79 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 79 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79 130))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 53 78 130 (Eq.refl Bool.true) (allA_succ_of_gcd 52 78 130 26 2 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 78 130 (Polychromatic418967fa.accept_12_3_6_10_1_576
  51 78 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 78 130 2 25 39 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 78 130
  (Polychromatic418967fa.accept_19_11_2_16_1_3822 49 78 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 78 130 2 24 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 78 130 (accept_3_3 47 78 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 78
  130 2 23 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  78 130 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 78 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 78 130 2 22 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 78 130 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 78 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 78 130 2 21 39 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 78 130 (accept_3_3 41 78 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 78 130 2 20 39 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 78 130 13 3 6 10 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 78 130 2 19 39 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 78 130
  (Polychromatic418967fa.accept_9_1_6_4_1_49 37 78 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 78 130 2 18 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 78 130 (accept_3_3 35 78 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 78
  130 2 17 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  78 130 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 78 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 78 130 2 16 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 78 130 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 78 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 130 2 15 39 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 130 (accept_3_3 29 78 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 78 130 2 14 39 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 78 130
  (Polychromatic418967fa.accept_12_3_6_10_1_576 27 78 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 78 130 26 1 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 78 130 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 78 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78 130 2 12 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 78 130 (accept_3_3 23 78 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78 130 2 11 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 78 130 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 78 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 78 130 2 10 39 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 78 130
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 78 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 78 130 2 9 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 78 130 (accept_3_3 17 78 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78
  130 2 8 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  78 130 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 78 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 78 130 2 7 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 13 78 130 13 1 6 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 12 78 130 2 6 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 78 130 (accept_3_3 11 78 130 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 78 130 2 5 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 78 130 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 78 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 78 130 2 4 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 78 130 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 78 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 130 2 3 39 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 130 (accept_3_3 5 78 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 130 2 2 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 78 130 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 78
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 78 130 2 1 39 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 130
  (Polychromatic418967fa.accept_9_1_6_4_1_49 1 78 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 78 130))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 77 130 (Eq.refl Bool.true)
  (allA_of_3_1 54 77 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 76 130 (Eq.refl Bool.true)
  (allA_succ_of_gcd 54 76 130 2 27 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 76 130 (accept_3_3 53 76 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 76
  130 2 26 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  76 130 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 76 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 76 130 2 25 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 76 130 (Polychromatic418967fa.accept_12_1_4_10_1_209 49 76 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 76 130 2 24 38 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 76 130 (accept_3_3 47 76 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 76 130 2 23 38 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 76 130
  (Polychromatic418967fa.accept_7_3_6_4_1_30 45 76 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 76 130 2 22 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 76 130 (Polychromatic418967fa.accept_12_7_4_10_1_572 43 76 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 76 130 2 21 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 76 130 (accept_3_3 41 76 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 76 130 2 20 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 76 130 (Polychromatic418967fa.accept_15_9_1_10_1_4316 39 76 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 76 130 2 19 38 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 76 130
  (Polychromatic418967fa.accept_7_2_6_4_1_29 37 76 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 76 130 2 18 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 76 130 (accept_3_3 35 76 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 76
  130 2 17 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  76 130 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 76 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 76 130 2 16 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 76 130 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 76 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 76 130 2 15 38 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 76 130 (accept_3_3 29 76 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 76 130 2 14 38 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 76 130
  (Polychromatic418967fa.accept_21_6_13_4_1_6521 27 76 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 76 130 2 13 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 76 130 (Polychromatic418967fa.accept_12_1_4_10_1_209 25 76 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 76 130 2 12 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 76 130 (accept_3_3 23 76 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 76 130 2 11 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 76 130 (Polychromatic418967fa.accept_15_6_1_10_1_1549 21 76 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 76 130 2 10 38 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 76 130
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 76 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 76 130 2 9 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 76 130 (accept_3_3 17 76 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 76
  130 2 8 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  76 130 (Polychromatic418967fa.accept_16_15_12_2_1_6502 15 76 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 76 130 2 7 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 76 130 (Polychromatic418967fa.accept_12_1_4_10_1_209 13 76 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 76 130 2 6 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 76 130 (accept_3_3 11 76 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 76 130 2 5 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 76 130 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 76 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 76 130 2 4 38 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 76 130
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 76 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 76 130 2 3 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 76 130 (accept_3_3 5 76 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 76 130
  2 2 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 76
  130 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 76 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 76 130 2 1 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 76 130 (Polychromatic418967fa.accept_11_1_10_9_1_871 1 76 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 76 130))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56
  75 130 (Eq.refl Bool.true) (allA_succ_of_gcd 55 75 130 5 11 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 75 130 (Polychromatic418967fa.accept_12_6_3_10_1_224 54 75 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 75 130 (accept_3_3 53 75 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 130 (Polychromatic418967fa.accept_9_7_3_4_1_218 52
  75 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 130
  (Polychromatic418967fa.accept_7_2_5_4_1_115 51 75 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 75 130 5 10 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 75 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 75 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 75 130 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 75 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 130 (accept_3_3 47 75 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 130 (Polychromatic418967fa.accept_9_1_3_4_1_47 46
  75 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75 130 5 9 15 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 75 130 (accept_3_3 44
  75 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 130
  (Polychromatic418967fa.accept_6_1_3_4_1_1 43 75 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 75 130 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 75 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 130 (accept_3_3 41 75 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 75 130 5 8 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 75 130 (Polychromatic418967fa.accept_16_7_11_2_1_3117 39 75 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 130 (accept_3_3 38 75 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 75 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 75 130
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 75 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 75 130 5 7 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 75 130 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 75 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 75 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 130 (accept_3_3 32 75 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 31
  75 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 75 130 5 6 15 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 75 130 (accept_3_3 29
  75 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 130
  (Polychromatic418967fa.accept_9_1_3_4_1_47 28 75 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 75 130 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 75 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 130 (accept_3_3 26 75 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 75 130 5 5 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 24 75 130 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 75 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 75 130 (accept_3_3 23 75 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 130 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 75 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 130
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 75 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 75 130 5 4 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 75 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 75 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 130 (Polychromatic418967fa.accept_12_6_3_10_1_224 18 75 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 130 (accept_3_3 17 75 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 130 (Polychromatic418967fa.accept_7_2_5_4_1_115 16
  75 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 130 5 3 15 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 130 (accept_3_3 14
  75 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 130
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 75 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 75 130 (Polychromatic418967fa.accept_20_12_15_10_1_6520 12 75 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 130 (accept_3_3 11 75 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 75 130 5 2 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 75 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 75 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 130 (accept_3_3 8 75 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 75 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 130
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 75 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 75 130 5 1 15 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 75 130 (Polychromatic418967fa.accept_20_4_15_10_1_6519 4 75 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 130 (Polychromatic418967fa.accept_19_3_18_16_1_6483 3 75 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 130 (accept_3_3 2 75 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 75
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  130)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 74 130 (Eq.refl Bool.true) (allA_of_3_1 57
  74 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 58 73 130 (Eq.refl Bool.true) (allA_succ_of_accept 57 73
  130 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 73 130 (accept_3_3 56 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  73 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 73 130 (Polychromatic418967fa.accept_16_6_9_2_1_6518 54 73 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 73 130 (accept_3_3 53 73 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 73 130 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 73 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 73 130
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 73 130 (accept_3_3 50 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  73 130 (Polychromatic418967fa.accept_11_5_7_9_1_2696 49 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 73 130 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 73 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 73 130 (accept_3_3 47 73 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 73 130 (Polychromatic418967fa.accept_11_2_7_9_1_890 46 73 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 73 130
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 73 130 (accept_3_3 44 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  73 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 73 130 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 73 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 73 130 (accept_3_3 41 73 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 73 130 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 73 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 73 130
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 73 130 (accept_3_3 38 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  73 130 (Polychromatic418967fa.accept_20_17_13_10_1_5059 37 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 73 130 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 73 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 73 130 (accept_3_3 35 73 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 73 130 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 73 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 73 130
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 73 130 (accept_3_3 32 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  73 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 73 130 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 73 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 73 130 (accept_3_3 29 73 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 73 130 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 73 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 73 130
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 73 130 (accept_3_3 26 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  73 130 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 73 130 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 73 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 73 130 (accept_3_3 23 73 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 73 130 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 73 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 73 130
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 73 130 (accept_3_3 20 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  73 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 73 130 (Polychromatic418967fa.accept_15_3_13_10_1_2332 18 73 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 73 130 (accept_3_3 17 73 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 73 130 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 73 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 73 130
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 73 130 (accept_3_3 14 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  73 130 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 73 130 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 73 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 73 130 (accept_3_3 11 73 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 73 130 (Polychromatic418967fa.accept_25_10_23_5_1_6517 10 73 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 73 130
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 73 130 (accept_3_3 8 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 73
  130 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 73 130 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 73 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 73 130 (accept_3_3 5 73 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 73 130 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 73 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 73 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 73
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 130 (accept_3_3 2 73 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 130 (Polychromatic418967fa.accept_7_1_3_4_1_128 1
  73 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  130)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 72 130 (Eq.refl Bool.true)
  (allA_succ_of_gcd 58 72 130 2 29 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 72 130 (Polychromatic418967fa.accept_17_6_4_11_1_4072 57 72 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 72 130 2 28 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 72 130 (Polychromatic418967fa.accept_7_6_2_4_1_291 55
  72 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 72 130 2 27 36 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 72 130 (accept_3_3 53
  72 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 72 130 2 26 36 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 72 130
  (Polychromatic418967fa.accept_14_9_2_4_1_1814 51 72 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 72 130 2 25 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 72 130 (Polychromatic418967fa.accept_17_15_4_11_1_6515 49 72 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 130 2 24 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 130 (accept_3_3 47 72 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 72 130 2 23 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 72 130 (Polychromatic418967fa.accept_20_5_12_10_1_5072 45 72
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 72 130 2 22 36 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 72 130
  (Polychromatic418967fa.accept_15_13_12_10_1_4352 43 72 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 72 130 2 21 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 72 130 (accept_3_3 41 72 130 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 72 130 2 20 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 72 130 (Polychromatic418967fa.accept_15_9_12_10_1_809 39 72 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 72 130 2 19 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 130 (Polychromatic418967fa.accept_14_9_2_4_1_1814
  37 72 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 130 2 18 36 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 130 (accept_3_3 35
  72 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72 130 2 17 36 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 72 130
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 72 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 72 130 2 16 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 72 130 (Polychromatic418967fa.accept_19_12_15_16_1_6516 31 72 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 130 2 15 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 130 (accept_3_3 29 72 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 72 130 2 14 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 72 130 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 72 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 72 130 2 13 36 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 130
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 25 72 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 72 130 2 12 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 72 130 (accept_3_3 23 72 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72
  130 2 11 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  72 130 (Polychromatic418967fa.accept_15_6_12_10_1_1543 21 72 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 72 130 2 10 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 72 130 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 72 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72 130 2 9 36 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 72 130 (accept_3_3 17 72 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72 130 2 8 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 72 130 (Polychromatic418967fa.accept_17_15_4_11_1_6515 15 72
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 130 2 7 36 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 130
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 72 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 72 130 2 6 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 72 130 (accept_3_3 11 72 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72
  130 2 5 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  72 130 (Polychromatic418967fa.accept_14_9_2_4_1_1814 9 72 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 72 130 2 4 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 72 130 (Polychromatic418967fa.accept_15_7_12_10_1_4335 7 72 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 130 2 3 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 130 (accept_3_3 5 72 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 130 2 2 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 72 130 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 72 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 130 2 1 36 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 130
  (Polychromatic418967fa.accept_19_1_15_16_1_2553 1 72 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 72 130))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 71 130 (Eq.refl Bool.true)
  (allA_of_3_1 60 71 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 70 130 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 70 130 10 6 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 70 130 (accept_3_3 59 70 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 70
  130 2 29 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  70 130 (Polychromatic418967fa.accept_9_3_7_4_1_53 57 70 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 70 130 2 28 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 55 70 130 5 11 14 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 70 130 2 27 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 70 130 (accept_3_3 53 70 130 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 70 130 2 26 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 70 130 (Polychromatic418967fa.accept_9_6_7_4_1_212 51 70 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 70 130 10 5 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 70 130 (Polychromatic418967fa.accept_16_1_6_2_1_3100 49 70 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 70 130 2 24 35 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 70 130 (accept_3_3 47
  70 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 70 130 2 23 35 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 70 130 5 9 14 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 70 130 2 22 35 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 70 130
  (Polychromatic418967fa.accept_16_11_6_2_1_4155 43 70 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 70 130 2 21 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 70 130 (accept_3_3 41 70 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 70
  130 10 4 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  70 130 (Polychromatic418967fa.accept_9_3_7_4_1_53 39 70 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 70 130 2 19 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 70 130 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 70 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 70 130 2 18 35 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 70 130 5 7 14 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 70 130 2 17 35 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 70 130
  (Polychromatic418967fa.accept_9_6_7_4_1_212 33 70 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 70 130 2 16 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 70 130 (Polychromatic418967fa.accept_19_12_13_16_1_6514 31 70 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 70 130 10 3 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 70 130 (accept_3_3 29 70 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 70 130 2 14 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 70 130 (Polychromatic418967fa.accept_16_11_6_2_1_4155 27 70 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 70 130 2 13 35 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 70 130 5 5 14 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 70 130 2 12 35 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 70 130 (accept_3_3 23 70 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 70 130 2 11 35 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 70 130
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 70 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 70 130 10 2 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 70 130 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 70 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 70 130 2 9 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 70 130 (accept_3_3 17 70 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 70 130 2 8 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 70 130 5 3 14 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 70 130 2 7 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 70 130 (Polychromatic418967fa.accept_11_2_4_9_1_484 13 70 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 70 130 2 6 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 70 130 (accept_3_3 11 70 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70 130 10 1 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 70 130 (Polychromatic418967fa.accept_16_9_6_2_1_3101 9 70 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 70 130 2 4 35 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 70 130
  (Polychromatic418967fa.accept_18_7_16_4_1_1674 7 70 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 70 130 2 3 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 70 130 5 1 14 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 70 130 2 2 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 70 130 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 70 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 70 130 2 1 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 70 130 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 70 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  130))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 69 130 (Eq.refl Bool.true)
  (allA_succ_of_accept 61 69 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 69 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 69 130 (Polychromatic418967fa.accept_18_6_15_4_1_3916 60 69
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 130 (accept_3_3 59 69 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 130 (Polychromatic418967fa.accept_7_2_6_4_1_29 58
  69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 130
  (Polychromatic418967fa.accept_9_3_6_4_1_210 57 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 69 130 (accept_3_3 56 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  69 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 69 130 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 69 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 130 (accept_3_3 53 69 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 130 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 69 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 130
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 69 130 (accept_3_3 50 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  69 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 69 130 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 69 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 130 (accept_3_3 47 69 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 130 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 69 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 130
  (Polychromatic418967fa.accept_7_3_6_4_1_30 45 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 69 130 (accept_3_3 44 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  69 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 69 130 (Polychromatic418967fa.accept_12_6_9_10_1_565 42 69 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 130 (accept_3_3 41 69 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 130 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 69 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 130
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 69 130 (accept_3_3 38 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  69 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 69 130 (Polychromatic418967fa.accept_20_16_9_10_1_6513 36 69 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 130 (accept_3_3 35 69 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 130 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 69 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 130
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 69 130 (accept_3_3 32 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  69 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 69 130 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 69 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 130 (accept_3_3 29 69 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 130 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 69 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 130
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 69 130 (accept_3_3 26 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  69 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 69 130 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 69 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 130 (accept_3_3 23 69 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 130 (Polychromatic418967fa.accept_25_22_19_5_1_6512 22 69 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 130
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 69 130 (accept_3_3 20 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  69 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 69 130 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 69 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 130 (accept_3_3 17 69 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 130 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 69 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 130
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 69 130 (accept_3_3 14 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  69 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 69 130 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 69 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 130 (accept_3_3 11 69 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 130 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 69 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 130
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 69 130 (accept_3_3 8 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69
  130 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 69 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 69 130 (Polychromatic418967fa.accept_11_6_3_9_1_906 6 69 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 130 (accept_3_3 5 69 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 69 130 (Polychromatic418967fa.accept_15_4_9_10_1_5384 4 69 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 69
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 130 (accept_3_3 2 69 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 69
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  130)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 68 130 (Eq.refl Bool.true)
  (allA_of_3_1 63 68 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 67 130 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 67 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 67 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 130 (accept_3_3 62 67 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 67 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 130
  (Polychromatic418967fa.accept_25_10_17_5_1_6511 60 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 130 (accept_3_3 59 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 130 (Polychromatic418967fa.accept_19_1_10_16_1_6510 58 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 130 (accept_3_3 56 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 130 (Polychromatic418967fa.accept_20_15_7_10_1_6509 55 67 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 130
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 54 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 130 (accept_3_3 53 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 130 (Polychromatic418967fa.accept_12_4_7_10_1_563 52 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 130 (accept_3_3 50 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 67 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 130
  (Polychromatic418967fa.accept_15_3_7_10_1_2324 48 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 130 (accept_3_3 47 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 130 (Polychromatic418967fa.accept_15_1_7_10_1_287 46 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 130 (accept_3_3 44 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 130 (Polychromatic418967fa.accept_11_10_1_9_1_2060 43 67 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 130
  (Polychromatic418967fa.accept_15_12_7_10_1_3297 42 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 130 (accept_3_3 41 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 130 (Polychromatic418967fa.accept_12_4_7_10_1_563 40 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 130 (accept_3_3 38 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 67 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 130
  (Polychromatic418967fa.accept_14_8_11_4_1_3438 36 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 130 (accept_3_3 35 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 130 (Polychromatic418967fa.accept_15_4_7_10_1_807 34 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 130 (accept_3_3 32 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 130 (Polychromatic418967fa.accept_15_1_7_10_1_287 31 67 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 130
  (Polychromatic418967fa.accept_22_8_1_20_1_6508 30 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 130 (accept_3_3 29 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 130 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 130 (accept_3_3 26 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 67 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 130
  (Polychromatic418967fa.accept_19_5_10_16_1_6507 24 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 130 (accept_3_3 23 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 130 (Polychromatic418967fa.accept_14_8_11_4_1_3438 22 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 130 (accept_3_3 20 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 130 (Polychromatic418967fa.accept_15_4_7_10_1_807 19 67 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 130
  (Polychromatic418967fa.accept_15_3_7_10_1_2324 18 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 130 (accept_3_3 17 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 130 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 130 (accept_3_3 14 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 67 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 130
  (Polychromatic418967fa.accept_15_12_7_10_1_3297 12 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 130 (accept_3_3 11 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 130 (Polychromatic418967fa.accept_11_10_1_9_1_2060 10 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 130 (accept_3_3 8 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 130 (Polychromatic418967fa.accept_14_7_11_4_1_3455 7 67 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 130
  (Polychromatic418967fa.accept_16_6_3_2_1_3096 6 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 130 (accept_3_3 5 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  130 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 67 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 67 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 130 (accept_3_3 2 67 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 67 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  130)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 66 130 (Eq.refl Bool.true)
  (allA_succ_of_gcd 64 66 130 2 32 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 66 130 (Polychromatic418967fa.accept_12_3_6_10_1_576 63 66 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 66 130 2 31 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 66 130 (Polychromatic418967fa.accept_9_7_3_4_1_218 61
  66 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 130 2 30 33 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 130 (accept_3_3 59
  66 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 130 2 29 33 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 130
  (Polychromatic418967fa.accept_7_1_3_4_1_128 57 66 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 66 130 2 28 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 66 130 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 66 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 66 130 2 27 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 66 130 (accept_3_3 53 66 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 66 130 2 26 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 66 130 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 66 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 66 130 2 25 33 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 66 130
  (Polychromatic418967fa.accept_14_7_10_4_1_130 49 66 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 66 130 2 24 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 66 130 (accept_3_3 47 66 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 66
  130 2 23 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  66 130 (Polychromatic418967fa.accept_12_9_6_10_1_1085 45 66 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 66 130 2 22 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 66 130 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 66 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 130 2 21 33 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 130 (accept_3_3 41 66 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 130 2 20 33 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 66 130
  (Polychromatic418967fa.accept_12_3_6_10_1_576 39 66 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 66 130 2 19 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 66 130 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 66 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66 130 2 18 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 66 130 (accept_3_3 35 66 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66 130 2 17 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 66 130 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 66 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 66 130 2 16 33 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 66 130
  (Polychromatic418967fa.accept_15_1_6_10_1_23 31 66 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 66 130 2 15 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 66 130 (accept_3_3 29 66 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66
  130 2 14 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  66 130 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 66 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 66 130 2 13 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 66 130 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 66 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 130 2 12 33 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 130 (accept_3_3 23 66 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 130 2 11 33 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 66 130
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 66 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 66 130 2 10 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 66 130 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 66 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 130 2 9 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 130 (accept_3_3 17 66 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 66 130 2 8 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 66 130 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 66 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 66 130 2 7 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 130 (Polychromatic418967fa.accept_7_6_3_4_1_294 13
  66 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 130 2 6 33 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 130 (accept_3_3 11
  66 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66 130 2 5 33 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 66 130
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 66 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 66 130 2 4 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 66 130 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 66 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 130 2 3 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 130 (accept_3_3 5 66 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 66 130 2 2 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 66 130 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 66 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 66 130 2 1 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 130 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 66
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  130))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 130 (allA_of_3_1 65 65 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 64 130 (allA_succ_of_accept 63 64 130
  (Polychromatic418967fa.accept_17_12_13_11_1_2910 63 64 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 64 130 2 31 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 64 130 (Polychromatic418967fa.accept_7_5_1_4_1_122 61 64 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 64 130 2 30 32 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 64 130 (accept_3_3 59 64 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 64 130 2 29 32 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 64 130
  (Polychromatic418967fa.accept_9_3_1_4_1_216 57 64 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 64 130 2 28 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 64 130 (Polychromatic418967fa.accept_12_7_4_10_1_572 55 64 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 64 130 2 27 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 64 130 (accept_3_3 53 64 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 64 130 2 26 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 64 130 (Polychromatic418967fa.accept_9_6_1_4_1_474 51 64 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 64 130 2 25 32 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 64 130
  (Polychromatic418967fa.accept_12_1_4_10_1_209 49 64 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 64 130 2 24 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 64 130 (accept_3_3 47 64 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 64
  130 2 23 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  64 130 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 64 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 64 130 2 22 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 64 130 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 64 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 64 130 2 21 32 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 64 130 (accept_3_3 41 64 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 64 130 2 20 32 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 64 130
  (Polychromatic418967fa.accept_9_3_1_4_1_216 39 64 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 64 130 2 19 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 64 130 (Polychromatic418967fa.accept_12_1_4_10_1_209 37 64 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 64 130 2 18 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 64 130 (accept_3_3 35 64 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 64 130 2 17 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 64 130 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 64 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 64 130 2 16 32 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 64 130
  (Polychromatic418967fa.accept_7_3_1_4_1_121 31 64 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 64 130 2 15 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 64 130 (accept_3_3 29 64 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 64
  130 2 14 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  64 130 (Polychromatic418967fa.accept_19_8_7_16_1_5117 27 64 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 64 130 2 13 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 64 130 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 64 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 64 130 2 12 32 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 64 130 (accept_3_3 23 64 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 64 130 2 11 32 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 64 130
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 64 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 64 130 2 10 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 64 130 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 64 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 64 130 2 9 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 64 130 (accept_3_3 17 64 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 64 130 2 8 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 64 130 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 64 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 64 130 2 7 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 64 130 (Polychromatic418967fa.accept_12_1_4_10_1_209
  13 64 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 64 130 2 6 32 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 64 130 (accept_3_3 11
  64 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64 130 2 5 32 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 64 130
  (Polychromatic418967fa.accept_15_9_4_10_1_2316 9 64 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 64 130 2 4 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 64 130 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 64 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 64 130 2 3 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 64 130 (accept_3_3 5 64 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 64 130 2 2 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 64 130 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 64 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 64 130 2 1 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 64 130 (Polychromatic418967fa.accept_12_1_4_10_1_209 1
  64 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  130)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 130 (allA_succ_of_accept 62 63 130
  (accept_3_3 62 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 63 130
  (Polychromatic418967fa.accept_4_1_3_2_1_3 61 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 63 130 (Polychromatic418967fa.accept_16_12_15_2_1_6473 60 63 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 130 (accept_3_3 59 63 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 63 130 (Polychromatic418967fa.accept_15_13_3_10_1_2296 58 63 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 130
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 63 130 (accept_3_3 56 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  63 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 63 130 (Polychromatic418967fa.accept_11_10_8_9_1_492 54 63 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 130 (accept_3_3 53 63 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 130 (Polychromatic418967fa.accept_14_10_7_4_1_3453 52 63 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 130
  (Polychromatic418967fa.accept_15_6_3_10_1_2341 51 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 63 130 (accept_3_3 50 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  63 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 63 130 (Polychromatic418967fa.accept_17_14_12_11_1_4063 48 63 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 130 (accept_3_3 47 63 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 130 (Polychromatic418967fa.accept_19_8_6_16_1_6505 46 63
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 130
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 63 130 (accept_3_3 44 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  63 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 63 130 (Polychromatic418967fa.accept_12_6_3_10_1_224 42 63 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 63 130 (accept_3_3 41 63 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 130 (Polychromatic418967fa.accept_17_6_12_11_1_5231 40 63 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 130
  (Polychromatic418967fa.accept_14_11_7_4_1_3449 39 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 63 130 (accept_3_3 38 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  63 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 63 130 (Polychromatic418967fa.accept_15_6_3_10_1_2341 36 63 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 130 (accept_3_3 35 63 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 130 (Polychromatic418967fa.accept_19_15_6_16_1_6506 34 63
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 130
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 63 130 (accept_3_3 32 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  63 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 63 130 (Polychromatic418967fa.accept_12_6_3_10_1_224 30 63 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 130 (accept_3_3 29 63 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 130 (Polychromatic418967fa.accept_15_13_3_10_1_2296 28 63 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 130
  (Polychromatic418967fa.accept_19_8_6_16_1_6505 27 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 63 130 (accept_3_3 26 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  63 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 63 130 (Polychromatic418967fa.accept_14_10_7_4_1_3453 24 63 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 130 (accept_3_3 23 63 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 130 (Polychromatic418967fa.accept_15_7_3_10_1_817 22 63 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 130
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 63 130 (accept_3_3 20 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  63 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 63 130 (Polychromatic418967fa.accept_12_6_3_10_1_224 18 63 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 130 (accept_3_3 17 63 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 130 (Polychromatic418967fa.accept_17_16_12_11_1_6504 16 63 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 130
  (Polychromatic418967fa.accept_18_15_9_4_1_5185 15 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 63 130 (accept_3_3 14 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  63 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 63 130 (Polychromatic418967fa.accept_16_12_15_2_1_6473 12 63 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 130 (accept_3_3 11 63 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 130 (Polychromatic418967fa.accept_11_10_8_9_1_492 10 63 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 130
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 130 (accept_3_3 8 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63
  130 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 63 130 (Polychromatic418967fa.accept_12_6_3_10_1_224 6 63 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 130 (accept_3_3 5 63 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 63 130 (Polychromatic418967fa.accept_27_4_9_22_1_6503 4 63 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 130 (Polychromatic418967fa.accept_14_3_7_4_1_118 3
  63 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 130 (accept_3_3 2 63 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 63
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  130))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 130 (allA_of_3_1 62 62 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 61 130 (allA_succ_of_accept 60 61 130
  (Polychromatic418967fa.accept_9_6_7_4_1_212 60 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 130 (accept_3_3 59 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 130 (Polychromatic418967fa.accept_7_2_5_4_1_115 58 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 61 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 130 (accept_3_3 56 61 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 61 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 130
  (Polychromatic418967fa.accept_15_9_1_10_1_4316 54 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 130 (accept_3_3 53 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 130 (Polychromatic418967fa.accept_12_4_1_10_1_221 52 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 61 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 130 (accept_3_3 50 61 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 130 (Polychromatic418967fa.accept_18_13_7_4_1_2738 49 61 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 130
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 130 (accept_3_3 47 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 130 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 61 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 130 (accept_3_3 44 61 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 61 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 130
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 130 (accept_3_3 41 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 130 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 61 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 130 (accept_3_3 38 61 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 130 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 61 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 130
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 130 (accept_3_3 35 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 130 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 61 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 130 (accept_3_3 32 61 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 61 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 130
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 130 (accept_3_3 29 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 130 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 61 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 130 (accept_3_3 26 61 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 130 (Polychromatic418967fa.accept_11_3_6_9_1_1378 25 61 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 130
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 130 (accept_3_3 23 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 130 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 61 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 130 (accept_3_3 20 61 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 61 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 130
  (Polychromatic418967fa.accept_17_1_10_11_1_2943 18 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 130 (accept_3_3 17 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 130 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 61 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 130 (accept_3_3 14 61 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 130 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 61 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 130
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 130 (accept_3_3 11 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 130 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 61 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 130 (accept_3_3 8 61 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 61 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 130
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 130 (accept_3_3 5 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  130 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 61 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 61 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 61 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 130 (accept_3_3 2 61 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 61 130 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 61 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61
  130))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 60 130 (allA_succ_of_accept 59 60 130
  (accept_3_3 59 60 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 60 130 2 29 30 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 60 130
  (Polychromatic418967fa.accept_9_3_6_4_1_210 57 60 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 60 130 2 28 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 55 60 130 5 11 12 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 54 60 130 2 27 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 60 130 (accept_3_3 53 60 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60
  130 2 26 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  60 130 (Polychromatic418967fa.accept_11_7_5_9_1_884 51 60 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 60 130 10 5 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 60 130 (Polychromatic418967fa.accept_16_1_12_2_1_2136 49 60 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60 130 2 24 30 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 60 130 (accept_3_3 47 60 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60 130 2 23 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 60 130 5 9 12 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 60 130 2 22 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 130 (Polychromatic418967fa.accept_9_7_6_4_1_483 43
  60 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 130 2 21 30 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 130 (accept_3_3 41
  60 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60 130 10 4 6 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 60 130
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 60 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 60 130 2 19 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 60 130 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 60 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 130 2 18 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 60 130 5 7 12 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 60 130 2 17 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 130 (Polychromatic418967fa.accept_16_1_12_2_1_2136
  33 60 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 60 130 2 16 30 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 60 130
  (Polychromatic418967fa.accept_16_15_12_2_1_6502 31 60 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 60 130 10 3 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 60 130 (accept_3_3 29 60 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60
  130 2 14 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  60 130 (Polychromatic418967fa.accept_21_6_18_4_1_4952 27 60 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 60 130 2 13 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 25 60 130 5 5 12 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 60 130 2 12 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 60 130 (accept_3_3 23 60 130 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 60 130 2 11 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 60 130 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 60 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 60 130 10 2 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 130 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 60 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 130 2 9 30 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 130 (accept_3_3 17 60 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60 130 2 8 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 60 130 5 3 12 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 60 130 2 7 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 130 (Polychromatic418967fa.accept_19_13_3_16_1_6467
  13 60 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 130 2 6 30 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 130 (accept_3_3 11
  60 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 130 10 1 6 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 60 130
  (Polychromatic418967fa.accept_16_9_12_2_1_3093 9 60 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 60 130 2 4 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 60 130 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 60 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 130 2 3 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 60 130 5 1 12 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 60 130 2 2 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 60 130 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 60 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 60 130 2 1 30 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 130
  (Polychromatic418967fa.accept_9_1_6_4_1_49 1 60 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 60 130)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 130 (allA_of_3_1 59 59 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 58 130 (allA_succ_of_accept 57 58 130
  (Polychromatic418967fa.accept_15_12_13_10_1_812 57 58 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 58 130 2 28 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 58 130 (Polychromatic418967fa.accept_7_6_2_4_1_291 55 58 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 58 130 2 27 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 58 130 (accept_3_3 53 58 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 58 130 2 26 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 58 130 (Polychromatic418967fa.accept_14_9_2_4_1_1814 51 58 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 58 130 2 25 29 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 58 130
  (Polychromatic418967fa.accept_15_4_13_10_1_1508 49 58 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 58 130 2 24 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 58 130 (accept_3_3 47 58 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 58
  130 2 23 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  58 130 (Polychromatic418967fa.accept_20_5_18_10_1_3565 45 58 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 58 130 2 22 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 58 130 (Polychromatic418967fa.accept_19_5_1_16_1_6501 43 58 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 58 130 2 21 29 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 58 130 (accept_3_3 41 58 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 58 130 2 20 29 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 58 130
  (Polychromatic418967fa.accept_11_6_3_9_1_906 39 58 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 58 130 2 19 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 58 130 (Polychromatic418967fa.accept_14_9_2_4_1_1814 37 58 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 58 130 2 18 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 58 130 (accept_3_3 35 58 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 58 130 2 17 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 58 130 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 58 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 58 130 2 16 29 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 58 130
  (Polychromatic418967fa.accept_15_1_13_10_1_1507 31 58 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 58 130 2 15 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 58 130 (accept_3_3 29 58 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 58
  130 2 14 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  58 130 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 58 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 58 130 2 13 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 58 130 (Polychromatic418967fa.accept_20_5_18_10_1_3565 25 58 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 58 130 2 12 29 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 58 130 (accept_3_3 23 58 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 58 130 2 11 29 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 58 130
  (Polychromatic418967fa.accept_27_21_4_22_1_6500 21 58 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 58 130 2 10 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 58 130 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 58 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 58 130 2 9 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 58 130 (accept_3_3 17 58 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 58 130 2 8 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 58 130 (Polychromatic418967fa.accept_19_15_1_16_1_6499 15 58 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 58 130 2 7 29 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 58 130
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 58 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 58 130 2 6 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 58 130 (accept_3_3 11 58 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58
  130 2 5 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  58 130 (Polychromatic418967fa.accept_14_9_2_4_1_1814 9 58 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 58 130 2 4 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 58 130 (Polychromatic418967fa.accept_20_7_18_10_1_6498 7 58 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 130 2 3 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 130 (accept_3_3 5 58 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 58 130 2 2 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 58 130 (Polychromatic418967fa.accept_15_3_13_10_1_2332 3 58 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 58 130 2 1 29 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 58 130
  (Polychromatic418967fa.accept_15_1_13_10_1_1507 1 58 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 58 130)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 130 (allA_succ_of_accept 56
  57 130 (accept_3_3 56 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 130
  (Polychromatic418967fa.accept_4_3_1_2_1_62 55 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 130 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 57 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 130 (accept_3_3 53 57 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 57 130 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 57 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 51
  57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 130 (accept_3_3 50 57
  130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 130 (Polychromatic418967fa.accept_6_1_3_4_1_1
  49 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 57 130
  (Polychromatic418967fa.accept_11_4_2_9_1_496 48 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 57 130 (accept_3_3 47 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  57 130 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 57 130 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 57 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 130 (accept_3_3 44 57 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 57 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 57 130
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 57 130 (accept_3_3 41 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  57 130 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 57 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 57 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 130 (accept_3_3 38 57 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 57 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 57 130
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 36 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 57 130 (accept_3_3 35 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  57 130 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 57 130 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 57 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 130 (accept_3_3 32 57 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 57 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 57 130
  (Polychromatic418967fa.accept_12_6_9_10_1_565 30 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 57 130 (accept_3_3 29 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  57 130 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 57 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 57 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 130 (accept_3_3 26 57 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 57 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 57 130
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 57 130 (accept_3_3 23 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  57 130 (Polychromatic418967fa.accept_15_7_12_10_1_4335 22 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 57 130 (Polychromatic418967fa.accept_15_6_12_10_1_1543 21 57 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 130 (accept_3_3 20 57 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 57 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 57 130
  (Polychromatic418967fa.accept_11_7_2_9_1_480 18 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 57 130 (accept_3_3 17 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  57 130 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 57 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 57 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 130 (accept_3_3 14 57 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 57 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 57 130
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 57 130 (accept_3_3 11 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  57 130 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 57 130 (Polychromatic418967fa.accept_15_9_12_10_1_809 9 57 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 130 (accept_3_3 8 57 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 57 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 130
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 130 (accept_3_3 5 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57
  130 (Polychromatic418967fa.accept_11_4_2_9_1_496 4 57 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 57 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 57 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 130 (accept_3_3 2 57 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 57 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 57 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 130)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 130 (allA_of_3_1 56 56 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 55 130
  (allA_succ_of_accept 54 55 130 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 55 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 130 (accept_3_3 53 55 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 55 130 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 55 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 51
  55 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 55 130 5 10 11 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 55 130
  (Polychromatic418967fa.accept_4_1_3_2_1_3 49 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 55 130 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 55 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 130 (accept_3_3 47 55 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 55 130 (Polychromatic418967fa.accept_19_8_17_16_1_6497 46 55 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 55 130 5 9 11 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 55 130 (accept_3_3 44 55 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 130 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 55 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 130
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 130 (accept_3_3 41 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 55
  130 5 8 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  55 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 55 130 (accept_3_3 38 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 55 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 55 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 130 (Polychromatic418967fa.accept_20_16_15_10_1_6496 36 55
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 55 130 5 7 11 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 55 130
  (Polychromatic418967fa.accept_9_7_1_4_1_217 34 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 55 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 55 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 130 (accept_3_3 32 55 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 55 130 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 55 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 55 130 5 6 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 55 130 (accept_3_3 29 55 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 130 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 55 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 130
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 130 (accept_3_3 26 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 55
  130 5 5 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  55 130 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 55 130 (accept_3_3 23 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 55 130 (Polychromatic418967fa.accept_19_3_17_16_1_6495 22 55 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 55 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 55 130 5 4 11 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 55 130
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 55 130 (Polychromatic418967fa.accept_19_18_17_16_1_6494 18 55 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 130 (accept_3_3 17 55 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 55 130 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 55 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 55 130 5 3 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 55 130 (accept_3_3 14 55 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 55 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 130
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 130 (accept_3_3 11 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 55
  130 5 2 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  55 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 55 130 (accept_3_3 8 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55
  130 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 55 130 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 55 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 55 130 5 1 11 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 55 130 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 55 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 130
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 55 130 (accept_3_3 2 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55
  130 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 55 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 55 130))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 130 (allA_succ_of_accept 53 54
  130 (accept_3_3 53 54 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 54 130 2 26 27 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 54 130
  (Polychromatic418967fa.accept_7_2_5_4_1_115 51 54 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 54 130 2 25 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 54 130 (Polychromatic418967fa.accept_15_4_9_10_1_5384 49 54 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 130 2 24 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 130 (accept_3_3 47 54 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 130 2 23 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 54 130 (Polychromatic418967fa.accept_11_1_10_9_1_871 45 54 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 54 130 2 22 27 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 54 130
  (Polychromatic418967fa.accept_7_1_5_4_1_134 43 54 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 54 130 2 21 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 54 130 (accept_3_3 41 54 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 54
  130 2 20 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  54 130 (Polychromatic418967fa.accept_12_3_6_10_1_576 39 54 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 54 130 2 19 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 54 130 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 54 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 130 2 18 27 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 130 (accept_3_3 35 54 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 54 130 2 17 27 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 54 130
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 54 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 54 130 2 16 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 54 130 (Polychromatic418967fa.accept_15_1_9_10_1_2327 31 54 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 130 2 15 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 130 (accept_3_3 29 54 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 130 2 14 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54 130 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 54 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 54 130 2 13 27 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 54 130
  (Polychromatic418967fa.accept_16_9_6_2_1_3101 25 54 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 130 2 12 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 54 130 (accept_3_3 23 54 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54
  130 2 11 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  54 130 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 54 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 54 130 2 10 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 54 130 (Polychromatic418967fa.accept_11_8_10_9_1_1401 19 54 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 130 2 9 27 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 130 (accept_3_3 17 54 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 130 2 8 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 54 130 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 54 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 54 130 2 7 27 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 130
  (Polychromatic418967fa.accept_7_6_5_4_1_297 13 54 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 54 130 2 6 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 54 130 (accept_3_3 11 54 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54
  130 2 5 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  54 130 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 54 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 54 130 2 4 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 54 130 (Polychromatic418967fa.accept_21_7_12_4_1_6493 7 54 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 130 2 3 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 130 (accept_3_3 5 54 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 130 2 2 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 54 130 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 54 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 54 130 2 1 27 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 130
  (Polychromatic418967fa.accept_7_1_5_4_1_134 1 54 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 54 130)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 130 (allA_of_3_1 53 53 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 52 130 (allA_succ_of_accept 51 52 130
  (Polychromatic418967fa.accept_9_6_7_4_1_212 51 52 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 52 130 2 25 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 52 130 (Polychromatic418967fa.accept_12_1_4_10_1_209 49 52 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 52 130 2 24 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 52 130 (accept_3_3 47 52 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 52 130 2 23 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 52 130 (Polychromatic418967fa.accept_20_5_12_10_1_5072 45 52
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 52 130 2 22 26 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 52 130
  (Polychromatic418967fa.accept_7_1_3_4_1_128 43 52 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 52 130 2 21 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 52 130 (accept_3_3 41 52 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 52
  130 2 20 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 52
  130 13 3 4 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 52
  130 2 19 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37
  52 130 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 52 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 52 130 2 18 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 52 130 (accept_3_3 35 52 130 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 52 130 2 17 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 52 130 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 52 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 52 130 2 16 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 52 130 (Polychromatic418967fa.accept_12_7_4_10_1_572
  31 52 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 52 130 2 15 26 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 52 130 (accept_3_3 29
  52 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 52 130 2 14 26 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 52 130
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 52 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 52 130 26 1 2 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 52 130 (Polychromatic418967fa.accept_12_1_4_10_1_209 25 52 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 52 130 2 12 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 52 130 (accept_3_3 23 52 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 52 130 2 11 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 52 130 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 52 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 52 130 2 10 26 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 52 130
  (Polychromatic418967fa.accept_9_1_7_4_1_52 19 52 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 52 130 2 9 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 52 130 (accept_3_3 17 52 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52
  130 2 8 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  52 130 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 52 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 52 130 2 7 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 13 52 130 13 1 4 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 12 52 130 2 6 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 52 130 (accept_3_3 11 52 130 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 52 130 2 5 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 52 130 (Polychromatic418967fa.accept_19_9_14_16_1_3791 9 52 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 52 130 2 4 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 52 130 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 52 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 52 130 2 3 26 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 52 130 (accept_3_3 5 52 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 52 130 2 2 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 52 130 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 52
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 52 130 2 1 26 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 52 130
  (Polychromatic418967fa.accept_7_1_3_4_1_128 1 52 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 52 130)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 130 (allA_succ_of_accept 50 51 130
  (accept_3_3 50 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 130
  (Polychromatic418967fa.accept_4_1_3_2_1_3 49 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 51 130 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 51 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 130 (accept_3_3 47 51 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 51 130 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 51 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 45
  51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 130 (accept_3_3 44 51
  130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 130 (Polychromatic418967fa.accept_6_1_3_4_1_1
  43 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 51 130
  (Polychromatic418967fa.accept_12_6_3_10_1_224 42 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 51 130 (accept_3_3 41 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  51 130 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 51 130 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 51 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 130 (accept_3_3 38 51 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 51 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 51 130
  (Polychromatic418967fa.accept_19_17_13_16_1_5118 36 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 130 (accept_3_3 35 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 51 130 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 51 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 51 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 130 (accept_3_3 32 51 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 31
  51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 51 130
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 51 130 (accept_3_3 29 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  51 130 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 51 130 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 51 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 130 (accept_3_3 26 51 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 51 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 51 130
  (Polychromatic418967fa.accept_11_2_7_9_1_890 24 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 51 130 (accept_3_3 23 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  51 130 (Polychromatic418967fa.accept_16_6_3_2_1_3096 22 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 51 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 51 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 130 (accept_3_3 20 51 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 51 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 51 130
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 51 130 (accept_3_3 17 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  51 130 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 51 130 (Polychromatic418967fa.accept_16_15_3_2_1_4170 15 51 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 130 (accept_3_3 14 51 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 51 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 130
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 51 130 (accept_3_3 11 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  51 130 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 51 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 51 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 130 (accept_3_3 8 51 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 51 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 130
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 130 (accept_3_3 5 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51
  130 (Polychromatic418967fa.accept_15_4_6_10_1_823 4 51 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 130 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 51 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 130 (accept_3_3 2 51 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 51 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  130))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 130 (allA_of_3_1 50 50 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 49 130 (allA_succ_of_accept 48 49 130 (Polychromatic418967fa.accept_21_6_7_4_1_4993 48
  49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 130 (accept_3_3 47 49
  130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 130
  (Polychromatic418967fa.accept_18_10_13_4_1_5153 46 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 49 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 49 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 130 (accept_3_3 44 49 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 49 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 49 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 49 130
  (Polychromatic418967fa.accept_19_4_11_16_1_1474 42 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 49 130 (accept_3_3 41 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  49 130 (Polychromatic418967fa.accept_11_7_5_9_1_884 40 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 49 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 49 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 130 (accept_3_3 38 49 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 130 (Polychromatic418967fa.accept_15_7_4_10_1_1513 37 49 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 130
  (Polychromatic418967fa.accept_15_6_4_10_1_2319 36 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 49 130 (accept_3_3 35 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  49 130 (Polychromatic418967fa.accept_19_15_11_16_1_6492 34 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 49 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 49 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 130 (accept_3_3 32 49 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 49 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 130
  (Polychromatic418967fa.accept_17_13_15_11_1_2936 30 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 49 130 (accept_3_3 29 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 49 130 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 49 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 49 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 130 (accept_3_3 26 49 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 130 (Polychromatic418967fa.accept_14_11_7_4_1_3449
  25 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 130
  (Polychromatic418967fa.accept_14_10_7_4_1_3453 24 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 130 (accept_3_3 23 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  49 130 (Polychromatic418967fa.accept_15_7_4_10_1_1513 22 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 49 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 49 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 130 (accept_3_3 20 49 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 49 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 130
  (Polychromatic418967fa.accept_11_7_5_9_1_884 18 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 130 (accept_3_3 17 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  49 130 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 49 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 49 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 130 (accept_3_3 14 49 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 130 (Polychromatic418967fa.accept_15_13_4_10_1_821 13 49 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 130
  (Polychromatic418967fa.accept_16_12_1_2_1_2163 12 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 49 130 (accept_3_3 11 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  49 130 (Polychromatic418967fa.accept_14_10_7_4_1_3453 10 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 49 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 49 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 130 (accept_3_3 8 49 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 49 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 130
  (Polychromatic418967fa.accept_15_6_4_10_1_2319 6 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 130 (accept_3_3 5 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  130 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 49 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 49 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 49 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 130 (accept_3_3 2 49 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 130 (Polychromatic418967fa.accept_20_1_9_10_1_6491 1 49 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 130)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 48 130 (allA_succ_of_accept 47 48 130 (accept_3_3 47 48 130 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 48 130 2 23 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 48 130 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 48 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 48 130 2 22 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 48 130 (Polychromatic418967fa.accept_9_7_3_4_1_218 43
  48 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 130 2 21 24 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 130 (accept_3_3 41
  48 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 130 2 20 24 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 48 130
  (Polychromatic418967fa.accept_15_9_3_10_1_2312 39 48 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 48 130 2 19 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 48 130 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 48 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 130 2 18 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 130 (accept_3_3 35 48 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48 130 2 17 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 48 130 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 48 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 48 130 2 16 24 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 48 130
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 48 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 48 130 2 15 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 48 130 (accept_3_3 29 48 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48
  130 2 14 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  48 130 (Polychromatic418967fa.accept_18_9_12_4_1_1659 27 48 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 48 130 2 13 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 48 130 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 48 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 130 2 12 24 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 130 (accept_3_3 23 48 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 130 2 11 24 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 48 130
  (Polychromatic418967fa.accept_15_6_3_10_1_2341 21 48 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 48 130 2 10 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 48 130 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 48 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 130 2 9 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 130 (accept_3_3 17 48 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 48 130 2 8 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 48 130 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 48 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 48 130 2 7 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 130 (Polychromatic418967fa.accept_11_2_4_9_1_484 13
  48 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 130 2 6 24 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 130 (accept_3_3 11
  48 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 130 2 5 24 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 48 130
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 48 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 48 130 2 4 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 48 130 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 48 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 130 2 3 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 130 (accept_3_3 5 48 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 48 130 2 2 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 48 130 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 48 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 130 2 1 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 130 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 48
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48
  130)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 130 (allA_of_3_1 47 47 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 46 130 (allA_succ_of_accept 45 46 130 (Polychromatic418967fa.accept_19_7_8_16_1_6490
  45 46 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 46 130 2 22 23 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 46 130
  (Polychromatic418967fa.accept_9_7_1_4_1_217 43 46 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 46 130 2 21 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 46 130 (accept_3_3 41 46 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 46
  130 2 20 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  46 130 (Polychromatic418967fa.accept_9_3_1_4_1_216 39 46 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 46 130 2 19 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 46 130 (Polychromatic418967fa.accept_11_4_2_9_1_496 37 46 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 46 130 2 18 23 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 46 130 (accept_3_3 35 46 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 46 130 2 17 23 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 46 130
  (Polychromatic418967fa.accept_9_6_1_4_1_474 33 46 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 46 130 2 16 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 46 130 (Polychromatic418967fa.accept_17_14_12_11_1_4063 31 46 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 46 130 2 15 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 46 130 (accept_3_3 29 46 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 46 130 2 14 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 46 130 (Polychromatic418967fa.accept_25_2_21_5_1_6489 27 46 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 46 130 2 13 23 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 46 130
  (Polychromatic418967fa.accept_9_7_1_4_1_217 25 46 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 46 130 2 12 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 46 130 (accept_3_3 23 46 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 46
  130 2 11 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  46 130 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 46 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 46 130 2 10 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 46 130 (Polychromatic418967fa.accept_20_19_6_10_1_3651 19 46 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 46 130 2 9 23 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 46 130 (accept_3_3 17 46 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 46 130 2 8 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 46 130 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 46 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 46 130 2 7 23 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 46 130
  (Polychromatic418967fa.accept_15_13_1_10_1_816 13 46 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 46 130 2 6 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 46 130 (accept_3_3 11 46 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46
  130 2 5 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  46 130 (Polychromatic418967fa.accept_15_9_1_10_1_4316 9 46 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 46 130 2 4 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 46 130 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 46 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 46 130 2 3 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 46 130 (accept_3_3 5 46 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 46 130 2 2 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 46 130 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 46 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 46 130 2 1 23 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 46 130
  (Polychromatic418967fa.accept_19_1_8_16_1_6488 1 46 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 46 130)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 130 (allA_succ_of_accept 44 45 130
  (accept_3_3 44 45 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 130
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 45 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 45 130 (Polychromatic418967fa.accept_12_6_9_10_1_565 42 45 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 130 (accept_3_3 41 45 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 45 130 5 8 9 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 45 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 45 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 130 (accept_3_3 38 45 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 45 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 130
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 45 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 45 130 5 7 9 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 45 130 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 45 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 130 (Polychromatic418967fa.accept_18_15_9_4_1_5185 33 45
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 130 (accept_3_3 32 45 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 31
  45 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45 130 5 6 9 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 130 (accept_3_3 29
  45 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 130
  (Polychromatic418967fa.accept_19_9_7_16_1_2591 28 45 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 45 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 45 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 130 (accept_3_3 26 45 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 45 130 5 5 9 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 24 45 130 (Polychromatic418967fa.accept_20_4_5_10_1_2308 24 45 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 130 (accept_3_3 23 45 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 130 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 45 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 130
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 45 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 45 130 5 4 9 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 45 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 45 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 130 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 45 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 130 (accept_3_3 17 45 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 130
  (Polychromatic418967fa.accept_20_16_5_10_1_6487 16 45 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 45 130 5 3 9 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 45 130 (accept_3_3 14 45 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  45 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 45 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 45 130 (Polychromatic418967fa.accept_18_12_9_4_1_2740 12 45 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 130 (accept_3_3 11 45 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 45 130 5 2 9 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 45 130 (Polychromatic418967fa.accept_19_9_7_16_1_2591 9 45 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 130 (accept_3_3 8 45 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 45
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 130
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 45 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 45 130 5 1 9 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 45 130 (Polychromatic418967fa.accept_19_4_7_16_1_6486 4 45 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 45 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 130 (accept_3_3 2 45 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 45
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  130))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 130 (allA_of_3_1 44 44 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 43 130 (allA_succ_of_accept 42 43 130 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 43 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 43 130 (accept_3_3 41 43 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 43 130 (Polychromatic418967fa.accept_7_5_1_4_1_122 40
  43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 130
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 43 130 (accept_3_3 38 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  43 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 43 130 (Polychromatic418967fa.accept_17_2_9_11_1_4057 36 43 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 43 130 (accept_3_3 35 43 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 43 130 (Polychromatic418967fa.accept_11_1_10_9_1_871 34 43 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 43 130
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 43 130 (accept_3_3 32 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  43 130 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 43 130 (Polychromatic418967fa.accept_9_3_7_4_1_53 30 43 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 130 (accept_3_3 29 43 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 43 130 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 43 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 130
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 43 130 (accept_3_3 26 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  43 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 43 130 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 43 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 43 130 (accept_3_3 23 43 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 43 130 (Polychromatic418967fa.accept_16_6_11_2_1_6485 22 43 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 130
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 43 130 (accept_3_3 20 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  43 130 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 43 130 (Polychromatic418967fa.accept_15_3_13_10_1_2332 18 43 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 43 130 (accept_3_3 17 43 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 43 130 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 43 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 43 130
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 43 130 (accept_3_3 14 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  43 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 43 130 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 43 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 130 (accept_3_3 11 43 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 43 130 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 43 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 130
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 43 130 (accept_3_3 8 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43
  130 (Polychromatic418967fa.accept_16_7_11_2_1_3117 7 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 43 130 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 43 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 43 130 (accept_3_3 5 43 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 43 130 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 43 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 43 130
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 43 130 (accept_3_3 2 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 43
  130 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 43 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 43 130))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 130 (allA_succ_of_accept 41 42 130
  (accept_3_3 41 42 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42 130 2 20 21 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 42 130
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 42 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 42 130 2 19 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 42 130 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 42 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 130 2 18 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 130 (accept_3_3 35 42 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 130 2 17 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42 130 (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 42 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 42 130 2 16 21 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 42 130
  (Polychromatic418967fa.accept_17_14_8_11_1_4052 31 42 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 42 130 2 15 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 42 130 (accept_3_3 29 42 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42
  130 2 14 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  42 130 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 42 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 42 130 2 13 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 42 130 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 42 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 130 2 12 21 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 130 (accept_3_3 23 42 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 130 2 11 21 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 42 130
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 42 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 42 130 2 10 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 42 130 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 42 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 130 2 9 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 130 (accept_3_3 17 42 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 42 130 2 8 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 42 130 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 42 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 130 2 7 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 130
  (Polychromatic418967fa.accept_15_13_12_10_1_4352 13 42 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 42 130 2 6 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 42 130 (accept_3_3 11 42 130 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 42 130 2 5 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 42 130 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 42 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 42 130 2 4 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 42 130 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 42 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 130 2 3 21 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 130 (accept_3_3 5 42 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 130 2 2 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 42 130 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 42
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 130 2 1 21 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 130
  (Polychromatic418967fa.accept_9_1_6_4_1_49 1 42 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 42 130)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 130 (allA_of_3_1 41 41 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 40 130 (allA_succ_of_accept 39 40 130
  (Polychromatic418967fa.accept_17_5_6_11_1_3974 39 40 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 40 130 2 19 20 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 40 130 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 40 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 40 130 2 18 20 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 40 130 5 7 8 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 40 130 2 17 20 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 40 130 (Polychromatic418967fa.accept_19_14_2_16_1_6484
  33 40 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 40 130 2 16 20 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 40 130
  (Polychromatic418967fa.accept_12_7_4_10_1_572 31 40 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 40 130 10 3 4 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 40 130 (accept_3_3 29 40 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 40
  130 2 14 20 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  40 130 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 40 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 40 130 2 13 20 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 25 40 130 5 5 8 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 40 130 2 12 20 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 40 130 (accept_3_3 23 40 130 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 40 130 2 11 20 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 40 130 (Polychromatic418967fa.accept_17_4_6_11_1_1030 21 40 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 40 130 10 2 4 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 40 130 (Polychromatic418967fa.accept_12_7_4_10_1_572 19 40 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 40 130 2 9 20 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 40 130 (accept_3_3 17 40 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 40 130 2 8 20 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 40 130 5 3 8 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 40 130 2 7 20 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 40 130 (Polychromatic418967fa.accept_7_6_5_4_1_297 13
  40 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 40 130 2 6 20 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 40 130 (accept_3_3 11
  40 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40 130 10 1 4 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 40 130
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 40 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 40 130 2 4 20 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 40 130 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 40 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 40 130 2 3 20 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 40 130 5 1 8 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 40 130 2 2 20 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 40 130 (Polychromatic418967fa.accept_19_3_2_16_1_5132 3 40 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 40 130 2 1 20 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 40 130
  (Polychromatic418967fa.accept_7_1_5_4_1_134 1 40 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 40 130)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 130 (allA_succ_of_accept 38 39 130 (accept_3_3
  38 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 130
  (Polychromatic418967fa.accept_4_1_3_2_1_3 37 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 39 130 (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 39 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 130 (accept_3_3 35 39 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 39 130 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 39 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 33
  39 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 130 (accept_3_3 32 39
  130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 130 (Polychromatic418967fa.accept_6_1_3_4_1_1
  31 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 39 130
  (Polychromatic418967fa.accept_12_6_3_10_1_224 30 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 39 130 (accept_3_3 29 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  39 130 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 39 130 (Polychromatic418967fa.accept_15_12_9_10_1_2326 27 39 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 39 130 13 2 3 10 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 39 130
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 39 130 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 39 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 130 (accept_3_3 23 39 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 39 130 (Polychromatic418967fa.accept_14_8_11_4_1_3438 22 39 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 130
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 39 130 (accept_3_3 20 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  39 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 39 130 (Polychromatic418967fa.accept_12_6_3_10_1_224 18 39 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 39 130 (accept_3_3 17 39 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 130 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 39 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 130
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 39 130 (accept_3_3 14 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 39
  130 13 1 3 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12
  39 130 (Polychromatic418967fa.accept_15_12_9_10_1_2326 12 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 130 (accept_3_3 11 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 130 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 39 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 39 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 130 (accept_3_3 8 39 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 39
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 130
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 130 (accept_3_3 5 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39
  130 (Polychromatic418967fa.accept_15_4_9_10_1_5384 4 39 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 130 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 39 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 130 (accept_3_3 2 39 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 39 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 130))))))))))))))))))))))))))))))))))))))) (allB_succ
  38 130 (allA_of_3_1 38 38 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 37 130 (allA_succ_of_accept 36 37
  130 (Polychromatic418967fa.accept_17_2_3_11_1_2919 36 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 37 130 (accept_3_3 35 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 37 130 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 37 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 37 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 130 (accept_3_3 32 37 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 31
  37 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 130
  (Polychromatic418967fa.accept_9_3_1_4_1_216 30 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 130 (accept_3_3 29 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 130 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 37 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 130 (accept_3_3 26 37 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 130 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 37 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 130
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 130 (accept_3_3 23 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 130 (Polychromatic418967fa.accept_19_3_18_16_1_6483 22 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 37 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 130 (accept_3_3 20 37 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 37 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 130
  (Polychromatic418967fa.accept_15_3_7_10_1_2324 18 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 130 (accept_3_3 17 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 130 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 37 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 130 (accept_3_3 14 37 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 130 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 37 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 130
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 130 (accept_3_3 11 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 130 (Polychromatic418967fa.accept_17_10_3_11_1_6482 10 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 37 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 130 (accept_3_3 8 37 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 37 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 130
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 130 (accept_3_3 5 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  130 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 37 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 37 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 37 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 130 (accept_3_3 2 37 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 37 130 (Polychromatic418967fa.accept_15_1_7_10_1_287 1 37 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 130))))))))))))))))))))))))))))))))))))) (allB_succ
  36 130 (allA_succ_of_accept 35 36 130 (accept_3_3 35 36 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  34 36 130 2 17 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 36 130 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 36 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 36 130 2 16 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 130 (Polychromatic418967fa.accept_7_3_1_4_1_121 31
  36 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 130 2 15 18 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 130 (accept_3_3 29
  36 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 130 2 14 18 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 130
  (Polychromatic418967fa.accept_15_12_6_10_1_1516 27 36 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 36 130 2 13 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 36 130 (Polychromatic418967fa.accept_14_11_8_4_1_2628 25 36 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 130 2 12 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 130 (accept_3_3 23 36 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 130 2 11 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 36 130 (Polychromatic418967fa.accept_19_2_17_16_1_6481 21 36
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 36 130 2 10 18 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 130
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 36 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 130 2 9 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 130 (accept_3_3 17 36 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36
  130 2 8 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  36 130 (Polychromatic418967fa.accept_20_15_16_10_1_6480 15 36 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 36 130 2 7 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 36 130 (Polychromatic418967fa.accept_19_13_17_16_1_6479 13 36 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 130 2 6 18 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 130 (accept_3_3 11 36 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36 130 2 5 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 36 130 (Polychromatic418967fa.accept_17_9_2_11_1_4042 9 36 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 36 130 2 4 18 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 130
  (Polychromatic418967fa.accept_19_7_17_16_1_6478 7 36 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 36 130 2 3 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 36 130 (accept_3_3 5 36 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 130
  2 2 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 36
  130 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 36 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 36 130 2 1 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 36 130 (Polychromatic418967fa.accept_15_1_6_10_1_23 1 36 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 36 130)))))))))))))))))))))))))))))))))))) (allB_succ 35 130 (allA_of_3_1 35
  35 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 34 130 (allA_succ_of_accept 33 34 130
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 34 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 34 130 2 16 17 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 34 130 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 34 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 34 130 2 15 17 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 34 130 (accept_3_3 29 34 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 34 130 2 14 17 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 34 130 (Polychromatic418967fa.accept_19_8_15_16_1_5109 27 34
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 34 130 2 13 17 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 34 130
  (Polychromatic418967fa.accept_18_7_16_4_1_1674 25 34 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 34 130 2 12 17 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 34 130 (accept_3_3 23 34 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34
  130 2 11 17 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  34 130 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 34 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 34 130 2 10 17 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 34 130 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 34 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 34 130 2 9 17 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 34 130 (accept_3_3 17 34 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 34 130 2 8 17 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 34 130 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 34 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 34 130 2 7 17 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 34 130
  (Polychromatic418967fa.accept_15_13_4_10_1_821 13 34 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 34 130 2 6 17 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 34 130 (accept_3_3 11 34 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34
  130 2 5 17 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  34 130 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 34 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 34 130 2 4 17 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 34 130 (Polychromatic418967fa.accept_15_7_4_10_1_1513 7 34 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 130 2 3 17 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 130 (accept_3_3 5 34 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 34 130 2 2 17 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 34 130 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 34 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 130 2 1 17 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 130
  (Polychromatic418967fa.accept_9_1_7_4_1_52 1 34 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 34 130)))))))))))))))))))))))))))))))))) (allB_succ 33 130 (allA_succ_of_accept 32 33 130 (accept_3_3 32 33
  130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 130 (Polychromatic418967fa.accept_4_3_1_2_1_62
  31 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 130
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 33 130 (accept_3_3 29 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  33 130 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 33 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 33 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 130 (accept_3_3 26 33 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 33 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 130
  (Polychromatic418967fa.accept_15_9_3_10_1_2312 24 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 33 130 (accept_3_3 23 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  33 130 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 33 130 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 33 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 130 (accept_3_3 20 33 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 33 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 130
  (Polychromatic418967fa.accept_12_6_9_10_1_565 18 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 33 130 (accept_3_3 17 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  33 130 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 33 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 33 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 130 (accept_3_3 14 33 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 33 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 130
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 33 130 (accept_3_3 11 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  33 130 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 33 130 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 33 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 130 (accept_3_3 8 33 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 33 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 130
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 130 (accept_3_3 5 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33
  130 (Polychromatic418967fa.accept_25_4_8_5_1_6477 4 33 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 33 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 33 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 130 (accept_3_3 2 33 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 33 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 130))))))))))))))))))))))))))))))))) (allB_succ 32
  130 (allA_of_3_1 32 32 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 130 (allA_succ_of_accept 30 31 130
  (Polychromatic418967fa.accept_23_7_8_15_1_6476 30 31 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 130 (accept_3_3 29 31 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  31 130 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 31 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 31 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 130 (accept_3_3 26 31 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 31 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 130
  (Polychromatic418967fa.accept_15_9_1_10_1_4316 24 31 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 130 (accept_3_3 23 31 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 130 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 31 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 31 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 130 (accept_3_3 20 31 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 130 (Polychromatic418967fa.accept_16_3_15_2_1_6475 19 31 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 130
  (Polychromatic418967fa.accept_22_18_9_20_1_6474 18 31 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 130 (accept_3_3 17 31 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 130 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 31 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 31 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 130 (accept_3_3 14 31 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 31 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 130
  (Polychromatic418967fa.accept_16_12_15_2_1_6473 12 31 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 130 (accept_3_3 11 31 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 130 (Polychromatic418967fa.accept_18_10_13_4_1_5153 10 31 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 31 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 130 (accept_3_3 8 31 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 130 (Polychromatic418967fa.accept_14_7_3_4_1_1816 7 31 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 130
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 31 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 130 (accept_3_3 5 31 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  130 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 31 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 31 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 31 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 130 (accept_3_3 2 31 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 31 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 130))))))))))))))))))))))))))))))) (allB_succ 30 130
  (allA_succ_of_accept 29 30 130 (accept_3_3 29 30 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30
  130 2 14 15 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  30 130 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 30 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 30 130 2 13 15 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 25 30 130 5 5 6 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 30 130 2 12 15 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 30 130 (accept_3_3 23 30 130 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 30 130 2 11 15 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 30 130 (Polychromatic418967fa.accept_11_10_8_9_1_492 21 30 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 30 130 10 2 3 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 130 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 30 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 130 2 9 15 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 130 (accept_3_3 17 30 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 130 2 8 15 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 30 130 5 3 6 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 30 130 2 7 15 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 130 (Polychromatic418967fa.accept_7_6_2_4_1_291 13
  30 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 130 2 6 15 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 130 (accept_3_3 11
  30 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 130 10 1 3 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 30 130
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 30 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 30 130 2 4 15 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 30 130 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 30 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 130 2 3 15 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 30 130 5 1 6 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 30 130 2 2 15 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 30 130 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 30 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 130 2 1 15 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 130
  (Polychromatic418967fa.accept_9_1_3_4_1_47 1 30 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 30 130)))))))))))))))))))))))))))))) (allB_succ 29 130 (allA_of_3_1 29 29 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 28 130 (allA_succ_of_accept 27 28 130 (Polychromatic418967fa.accept_15_12_13_10_1_812 27 28 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 28 130 2 13 14 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 28 130
  (Polychromatic418967fa.accept_9_7_1_4_1_217 25 28 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 28 130 2 12 14 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 28 130 (accept_3_3 23 28 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 28
  130 2 11 14 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  28 130 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 28 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 28 130 2 10 14 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 28 130 (Polychromatic418967fa.accept_12_7_4_10_1_572 19 28 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 28 130 2 9 14 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 28 130 (accept_3_3 17 28 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 28 130 2 8 14 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 28 130 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 28 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 28 130 2 7 14 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 28 130
  (Polychromatic418967fa.accept_12_1_4_10_1_209 13 28 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 28 130 2 6 14 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 28 130 (accept_3_3 11 28 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 28
  130 2 5 14 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  28 130 (Polychromatic418967fa.accept_16_9_12_2_1_3093 9 28 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 28 130 2 4 14 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 28 130 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 28 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 28 130 2 3 14 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 28 130 (accept_3_3 5 28 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 28 130 2 2 14 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 28 130 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 28 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 28 130 2 1 14 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 28 130
  (Polychromatic418967fa.accept_12_1_4_10_1_209 1 28 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 28 130)))))))))))))))))))))))))))) (allB_succ 27 130 (allA_succ_of_accept 26 27 130 (accept_3_3 26 27 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 25
  27 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 130
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 27 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 27 130 (accept_3_3 23 27 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  27 130 (Polychromatic418967fa.accept_15_7_12_10_1_4335 22 27 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 27 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 27 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 130 (accept_3_3 20 27 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 27 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 130
  (Polychromatic418967fa.accept_11_7_5_9_1_884 18 27 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 27 130 (accept_3_3 17 27 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  27 130 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 27 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 27 130 (Polychromatic418967fa.accept_18_15_9_4_1_5185 15 27 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 130 (accept_3_3 14 27 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 27 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 130
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 27 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 27 130 (accept_3_3 11 27 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  27 130 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 27 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 27 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 27 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 130 (accept_3_3 8 27 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 27 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27 130
  (Polychromatic418967fa.accept_12_6_3_10_1_224 6 27 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 130 (accept_3_3 5 27 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27
  130 (Polychromatic418967fa.accept_17_4_10_11_1_6472 4 27 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 27 130 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 27 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 130 (accept_3_3 2 27 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 27 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 130))))))))))))))))))))))))))) (allB_succ 26 130
  (allA_of_3_1 26 26 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 25 130 (allA_succ_of_accept 24 25 130
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 25 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 130 (accept_3_3 23 25 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 130 (Polychromatic418967fa.accept_14_8_11_4_1_3438 22 25 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 25 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 25 130 5 4 5 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 25 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 19
  25 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 130
  (Polychromatic418967fa.accept_17_1_8_11_1_6471 18 25 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 130 (accept_3_3 17 25 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 130 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 25 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 25 130 5 3 5 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 25 130 (accept_3_3 14 25 130 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 25 130 (Polychromatic418967fa.accept_18_13_7_4_1_2738 13 25 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 130 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 25 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 130 (accept_3_3 11 25 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 25 130 5 2 5 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 25 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 25
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 130 (accept_3_3 8 25 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 25
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 130
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 25 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 25 130 5 1 5 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 25 130 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 25 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 25 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 130 (accept_3_3 2 25 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 130 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 25
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 130))))))))))))))))))))))))) (allB_succ
  24 130 (allA_succ_of_accept 23 24 130 (accept_3_3 23 24 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  22 24 130 2 11 12 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 24 130 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 24 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 24 130 2 10 12 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 24 130 (Polychromatic418967fa.accept_9_1_6_4_1_49 19
  24 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 130 2 9 12 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 130 (accept_3_3 17
  24 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 24 130 2 8 12 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 24 130
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 24 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 24 130 2 7 12 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 24 130 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 24 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 130 2 6 12 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 130 (accept_3_3 11 24 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 24 130 2 5 12 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 24 130 (Polychromatic418967fa.accept_23_9_1_15_1_6470 9 24 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 24 130 2 4 12 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 24 130 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 24
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 130 2 3 12 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 130 (accept_3_3 5 24
  130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 130 2 2 12 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 24 130
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 24 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 24 130 2 1 12 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 24 130 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 24 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 24 130)))))))))))))))))))))))) (allB_succ 23 130 (allA_of_3_1 23 23 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 22 130 (allA_succ_of_accept 21 22 130
  (Polychromatic418967fa.accept_19_2_3_16_1_6469 21 22 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 22 130 2 10 11 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 22 130 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 22 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 22 130 2 9 11 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 22 130 (accept_3_3 17 22 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 22 130 2 8 11 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 22 130 (Polychromatic418967fa.accept_17_15_5_11_1_6468 15 22 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 22 130 2 7 11 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 22 130
  (Polychromatic418967fa.accept_19_13_3_16_1_6467 13 22 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 22 130 2 6 11 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 22 130 (accept_3_3 11 22 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 22
  130 2 5 11 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  22 130 (Polychromatic418967fa.accept_16_9_6_2_1_3101 9 22 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 22 130 2 4 11 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 22 130 (Polychromatic418967fa.accept_17_7_5_11_1_2922 7 22 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 22 130 2 3 11 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 22 130 (accept_3_3 5 22 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 22 130 2 2 11 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 22 130 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 22 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 22 130 2 1 11 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 22 130
  (Polychromatic418967fa.accept_15_1_7_10_1_287 1 22 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 22 130)))))))))))))))))))))) (allB_succ 21 130 (allA_succ_of_accept 20 21 130 (accept_3_3 20 21 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 21 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 130
  (Polychromatic418967fa.accept_12_6_9_10_1_565 18 21 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 21 130 (accept_3_3 17 21 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  21 130 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 21 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 21 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 21 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 130 (accept_3_3 14 21 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 21 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 130
  (Polychromatic418967fa.accept_11_1_10_9_1_871 12 21 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 21 130 (accept_3_3 11 21 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  21 130 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 21 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 21 130 (Polychromatic418967fa.accept_20_9_1_10_1_6466 9 21 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 130 (accept_3_3 8 21 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 21 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 130
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 21 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 130 (accept_3_3 5 21 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21
  130 (Polychromatic418967fa.accept_15_4_6_10_1_823 4 21 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 21 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 21 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 130 (accept_3_3 2 21 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 21 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 130))))))))))))))))))))) (allB_succ 20 130
  (allA_of_3_1 20 20 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 130 (allA_succ_of_accept 18 19 130
  (Polychromatic418967fa.accept_21_18_19_4_1_4979 18 19 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 130 (accept_3_3 17 19 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 130 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 19 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 19 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 130 (accept_3_3 14 19 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 19 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 130
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 19 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 130 (accept_3_3 11 19 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 130 (Polychromatic418967fa.accept_11_10_8_9_1_492 10 19 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 19 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 130 (accept_3_3 8 19 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 130 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 19 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 130
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 19 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 130 (accept_3_3 5 19 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  130 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 19 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 19 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 19 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 130 (accept_3_3 2 19 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 19 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 19 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 130))))))))))))))))))) (allB_succ 18 130
  (allA_succ_of_accept 17 18 130 (accept_3_3 17 18 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18
  130 2 8 9 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  18 130 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 18 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 18 130 2 7 9 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 18 130 (Polychromatic418967fa.accept_11_2_7_9_1_890 13 18 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 130 2 6 9 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 130 (accept_3_3 11 18 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 18 130 2 5 9 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 18 130 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 18 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 130 2 4 9 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 130
  (Polychromatic418967fa.accept_15_7_3_10_1_817 7 18 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 18 130 2 3 9 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 18 130 (accept_3_3 5 18 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 130
  2 2 9 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 130
  (Polychromatic418967fa.accept_12_3_6_10_1_576 3 18 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 130 2 1 9 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 130 (Polychromatic418967fa.accept_21_1_18_4_1_4975 1 18 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 18 130)))))))))))))))))) (allB_succ 17 130 (allA_of_3_1 17 17 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 16 130 (allA_succ_of_accept 15 16 130
  (Polychromatic418967fa.accept_9_6_7_4_1_212 15 16 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 16 130 2 7 8 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 16 130 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 16 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 16 130 2 6 8 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 16 130 (accept_3_3 11 16 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 16 130 2 5 8 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 16 130 (Polychromatic418967fa.accept_14_9_2_4_1_1814 9 16 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 16 130 2 4 8 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 16 130 (Polychromatic418967fa.accept_11_7_5_9_1_884 7
  16 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 130 2 3 8 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 130 (accept_3_3 5 16
  130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 130 2 2 8 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 16 130
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 16 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 16 130 2 1 8 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 16 130 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 16 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 16 130)))))))))))))))) (allB_succ 15 130 (allA_succ_of_accept 14 15 130
  (accept_3_3 14 15 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 130
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 15 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 15 130 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 15 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 130 (accept_3_3 11 15 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 15 130 5 2 3 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 15 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 15 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 130 (accept_3_3 8 15 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 15 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 130
  (Polychromatic418967fa.accept_12_6_3_10_1_224 6 15 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 15 130 5 1 3 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 15 130 (Polychromatic418967fa.accept_17_4_15_11_1_6465 4 15 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 130 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 15 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 130 (accept_3_3 2 15 130
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 15
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 130))))))))))))))) (allB_succ 14 130
  (allA_of_3_1 14 14 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 130 (allA_succ_of_accept 12 13 130
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 13 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 130 (accept_3_3 11 13 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 130 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 13 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 13 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 130 (accept_3_3 8 13 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 13 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 130
  (Polychromatic418967fa.accept_17_6_13_11_1_995 6 13 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 130 (accept_3_3 5 13 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  130 (Polychromatic418967fa.accept_11_4_2_9_1_496 4 13 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 13 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 130 (accept_3_3 2 13 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 130 (Polychromatic418967fa.accept_15_1_13_10_1_1507 1 13 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 130))))))))))))) (allB_succ 12 130 (allA_succ_of_accept 11 12
  130 (accept_3_3 11 12 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12 130 2 5 6 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 12 130
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 12 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 12 130 2 4 6 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 12 130 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 12 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 130 2 3 6 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 130 (accept_3_3 5 12 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 12 130 2 2 6 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 12 130 (Polychromatic418967fa.accept_20_3_12_10_1_6464 3 12 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 130 2 1 6 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 130 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 12
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 130)))))))))))) (allB_succ 11 130
  (allA_of_3_1 11 11 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 10 130 (allA_succ_of_accept 9 10 130
  (Polychromatic418967fa.accept_19_9_10_16_1_6463 9 10 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 10 130 2 4 5 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 10 130 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 10 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 10 130 2 3 5 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 10 130 5 1 2 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 10 130 2 2 5 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 10 130 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 10 130
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 10 130 2 1 5 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 10 130
  (Polychromatic418967fa.accept_7_1_3_4_1_128 1 10 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 10 130)))))))))) (allB_succ 9 130 (allA_succ_of_accept 8 9 130 (accept_3_3 8 9 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 9 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 130
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 9 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 130 (accept_3_3 5 9 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 130
  (Polychromatic418967fa.accept_15_4_9_10_1_5384 4 9 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 9 130 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 9 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 130 (accept_3_3 2 9 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 9 130 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 9 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 130))))))))) (allB_succ 8 130 (allA_of_3_1 8 8 130 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 7 130 (allA_succ_of_accept 6 7 130
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 7 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 130 (accept_3_3 5 7 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 130
  (Polychromatic418967fa.accept_12_4_7_10_1_563 4 7 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 130 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 7 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 130 (accept_3_3 2 7 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 7 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 130))))))) (allB_succ 6 130 (allA_succ_of_accept 5 6 130
  (accept_3_3 5 6 130 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 130 2 2 3 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 130
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 6 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 130 2 1 3 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 130 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 6 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 6 130)))))) (allB_succ 5 130 (allA_of_3_1 5 5 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 4 130 (allA_succ_of_accept 3 4 130 (Polychromatic418967fa.accept_19_3_4_16_1_6462 3 4
  130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 4 130 2 1 2 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 4 130
  (Polychromatic418967fa.accept_12_1_4_10_1_209 1 4 130 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 130)))) (allB_succ 3 130 (allA_succ_of_accept 2 3 130 (accept_3_3 2 3 130 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 130 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 3 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 130))) (allB_succ 2 130 (allA_of_3_1 2 2 130 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  130))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


