-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch134
-- name    : Polychromatic418967fa_Branch134
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:13:09.278504+00:00
-- url     : https://prove2.me/theorems/530eb6d1-57e4-4360-a691-69935d2a472c
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

def Polychromatic418967fa.branch_134 : allB 134 134 :=
  allB_succ' 2 133 134 (Eq.refl Bool.true) (allA_of_3_0 2 133 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  132 134 (Eq.refl Bool.true) (allA_succ_of_gcd 2 132 134 2 1 66 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 134 (accept_3_2 1 132 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 132 134))) (allB_succ' 4 131 134 (Eq.refl Bool.true) (allA_succ_of_accept 3 131 134
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 131 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 131 134 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 131 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 131 134 (accept_3_2 1 131 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 131 134)))) (allB_succ' 5 130 134 (Eq.refl Bool.true) (allA_of_3_0 5 130 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 6 129 134 (Eq.refl Bool.true) (allA_succ_of_accept 5 129 134
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 129 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 129 134 (accept_3_2 4 129 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  129 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 129 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 129 134 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 129 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 134 (accept_3_2 1 129 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 129 134)))))) (allB_succ' 7 128 134 (Eq.refl Bool.true) (allA_succ_of_gcd 6 128 134 2 3
  64 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 128 134
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 128 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 128 134 2 2 64 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 128 134 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 128 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 128 134 2 1 64 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 128 134 (accept_3_2 1 128 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 128 134))))))) (allB_succ' 8 127 134 (Eq.refl Bool.true) (allA_of_3_0 8 127 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 9 126 134 (Eq.refl Bool.true) (allA_succ_of_gcd 8 126 134 2 4 63 67
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 126 134
  (accept_3_2 7 126 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 126 134 2 3 63 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 126 134
  (Polychromatic418967fa.accept_10_5_6_4_1_64 5 126 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 126 134 2 2 63 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 126 134 (Polychromatic418967fa.accept_12_3_6_2_1_747 3 126 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 126 134 2 1 63 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 126 134 (accept_3_2 1 126 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 126 134))))))))) (allB_succ' 10 125 134 (Eq.refl Bool.true) (allA_succ_of_accept 9 125 134
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 125 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 125 134 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 125 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 125 134 (accept_3_2 7 125 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 125 134 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 125 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 125 134 (Polychromatic418967fa.accept_7_5_6_1_1_407 5
  125 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 125 134 (accept_3_2 4 125
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 134 (Polychromatic418967fa.accept_4_3_1_2_1_62
  3 125 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 134
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 125 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 134 (accept_3_2 1 125 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  134)))))))))) (allB_succ' 11 124 134 (Eq.refl Bool.true) (allA_of_3_0 11 124 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 123 134 (Eq.refl Bool.true) (allA_succ_of_accept 11 123 134
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 123 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 123 134 (accept_3_2 10 123 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  123 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 123 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 123 134 (Polychromatic418967fa.accept_19_8_9_1_1_3990 8 123 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 134 (accept_3_2 7 123 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 134 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 123 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 134
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 123 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 123 134 (accept_3_2 4 123 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  123 134 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 123 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 123 134 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 123 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 134 (accept_3_2 1 123 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 123 134)))))))))))) (allB_succ' 13 122 134 (Eq.refl Bool.true) (allA_succ_of_gcd 12 122
  134 2 6 61 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  122 134 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 122 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 122 134 2 5 61 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 122 134 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 122 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 122 134 2 4 61 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 122 134 (accept_3_2 7 122 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 122 134 2 3 61 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 122 134 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 122 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 122 134 2 2 61 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 122 134
  (Polychromatic418967fa.accept_9_3_5_8_1_99 3 122 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 122 134 2 1 61 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 122 134 (accept_3_2 1 122 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  134))))))))))))) (allB_succ' 14 121 134 (Eq.refl Bool.true) (allA_of_3_0 14 121 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 120 134 (Eq.refl Bool.true) (allA_succ_of_gcd 14 120 134 2 7 60 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 120 134 (accept_3_2 13 120 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 134 2 6 60 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 134
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 120 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 120 134 2 5 60 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 120 134 (Polychromatic418967fa.accept_17_9_1_15_1_3156 9 120 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 120 134 2 4 60 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 120 134 (accept_3_2 7 120 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 120 134 2 3 60 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 120 134 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 120 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 120 134 2 2 60 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 120 134 (Polychromatic418967fa.accept_17_3_1_15_1_6835
  3 120 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 120 134 2 1 60 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 134 (accept_3_2 1
  120 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120 134))))))))))))))) (allB_succ' 16 119 134 (Eq.refl
  Bool.true) (allA_succ_of_accept 15 119 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 119 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 134 (Polychromatic418967fa.accept_9_5_2_8_1_109
  14 119 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 119 134 (accept_3_2 13
  119 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 119 134
  (Polychromatic418967fa.accept_9_3_2_8_1_108 12 119 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 119 134 (Polychromatic418967fa.accept_13_11_2_4_1_1590 11 119 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 134 (accept_3_2 10 119 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 119 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 119 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 134 (Polychromatic418967fa.accept_10_8_9_4_1_961 8
  119 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 119 134 (accept_3_2 7 119
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 119 134
  (Polychromatic418967fa.accept_9_6_2_8_1_592 6 119 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 119 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 119 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 134 (accept_3_2 4 119 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 119 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 119 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 134 (Polychromatic418967fa.accept_21_2_14_8_1_6834
  2 119 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 119 134 (accept_3_2 1
  119 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119 134)))))))))))))))) (allB_succ' 17 118 134 (Eq.refl
  Bool.true) (allA_of_3_0 17 118 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 18 117 134 (Eq.refl Bool.true)
  (allA_succ_of_accept 17 117 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 117 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 134 (accept_3_2 16 117 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 117 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 117 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 134
  (Polychromatic418967fa.accept_21_14_12_8_1_6833 14 117 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 117 134 (accept_3_2 13 117 134 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 117 134 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 117 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 117 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 117 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 134 (accept_3_2 10 117 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 134 (Polychromatic418967fa.accept_11_9_7_2_1_1068
  9 117 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 134
  (Polychromatic418967fa.accept_23_8_2_19_1_6832 8 117 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 117 134 (accept_3_2 7 117 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  117 134 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 117 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 117 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 117 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 134 (accept_3_2 4 117 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 117 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 134
  (Polychromatic418967fa.accept_10_2_7_4_1_967 2 117 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 117 134 (accept_3_2 1 117 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  134)))))))))))))))))) (allB_succ' 19 116 134 (Eq.refl Bool.true) (allA_succ_of_gcd 18 116 134 2 9 58 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 116 134
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 116 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 116 134 2 8 58 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 116 134 (Polychromatic418967fa.accept_10_5_6_4_1_64 15 116 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 116 134 2 7 58 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 116 134 (accept_3_2 13 116 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 116 134 2 6 58 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 116 134 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 116
  134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 116 134 2 5 58 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 116 134
  (Polychromatic418967fa.accept_19_9_2_1_1_2821 9 116 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 116 134 2 4 58 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 116 134 (accept_3_2 7 116 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 116
  134 2 3 58 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  116 134 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 116 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 116 134 2 2 58 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 116 134 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 116 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 116 134 2 1 58 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 116 134 (accept_3_2 1 116 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 116 134))))))))))))))))))) (allB_succ' 20 115 134 (Eq.refl Bool.true) (allA_of_3_0 20
  115 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 114 134 (Eq.refl Bool.true) (allA_succ_of_gcd 20 114
  134 2 10 57 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19
  114 134 (accept_3_2 19 114 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 114 134 2 9 57 67
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 114 134
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 114 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 114 134 2 8 57 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 114 134 (Polychromatic418967fa.accept_12_3_6_2_1_747 15 114 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 114 134 2 7 57 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 114 134 (accept_3_2 13 114 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 114 134 2 6 57 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 114 134 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 114 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 114 134 2 5 57 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 114 134
  (Polychromatic418967fa.accept_11_9_4_2_1_600 9 114 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 114 134 2 4 57 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 114 134 (accept_3_2 7 114 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114
  134 2 3 57 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  114 134 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 114 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 114 134 2 2 57 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 114 134 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 114 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 114 134 2 1 57 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 134 (accept_3_2 1 114 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 114 134))))))))))))))))))))) (allB_succ' 22 113 134 (Eq.refl Bool.true)
  (allA_succ_of_accept 21 113 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 113 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 134 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 113 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 113 134 (accept_3_2 19 113 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 113 134 (Polychromatic418967fa.accept_13_5_9_4_1_441
  18 113 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 113 134
  (Polychromatic418967fa.accept_10_7_3_4_1_978 17 113 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 113 134 (accept_3_2 16 113 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 113 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 113 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 113 134 (Polychromatic418967fa.accept_18_14_5_8_1_1880 14 113 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 113 134 (accept_3_2 13 113 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 113 134 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 113 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 113 134
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 113 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 113 134 (accept_3_2 10 113 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  113 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 113 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 113 134 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 113 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 113 134 (accept_3_2 7 113 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 113 134 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 113 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 113 134
  (Polychromatic418967fa.accept_13_5_9_4_1_441 5 113 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 113 134 (accept_3_2 4 113 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  113 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 113 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 113 134 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 113 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 113 134 (accept_3_2 1 113 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 113 134)))))))))))))))))))))) (allB_succ' 23 112 134 (Eq.refl Bool.true) (allA_of_3_0
  23 112 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 111 134 (Eq.refl Bool.true) (allA_succ_of_accept 23
  111 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 111 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 111 134 (accept_3_2 22 111 134 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 111 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 111 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 134 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 111 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 134 (accept_3_2 19 111 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 134 (Polychromatic418967fa.accept_12_6_3_2_1_743
  18 111 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 134
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 111 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 111 134 (accept_3_2 16 111 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 111 134 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 111 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 111 134 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 111 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 134 (accept_3_2 13 111 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 134 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 111 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 134
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 111 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 134 (accept_3_2 10 111 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  111 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 111 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 111 134 (Polychromatic418967fa.accept_15_8_6_14_1_975 8 111 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 134 (accept_3_2 7 111 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 134 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 111 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 134
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 111 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 134 (accept_3_2 4 111 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  111 134 (Polychromatic418967fa.accept_11_3_1_2_1_1063 3 111 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 111 134 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 111 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 134 (accept_3_2 1 111 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 111 134)))))))))))))))))))))))) (allB_succ' 25 110 134 (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 110 134 2 12 55 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 110 134 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 110 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 110 134 2 11 55 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 110 134
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 110 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 110 134 2 10 55 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 110 134 (accept_3_2 19 110 134 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 110 134 2 9 55 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 110 134 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 110 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 110 134 2 8 55 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 110 134 (Polychromatic418967fa.accept_9_6_2_8_1_592 15
  110 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 110 134 2 7 55 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 110 134 (accept_3_2 13
  110 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 110 134 2 6 55 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 110 134
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 110 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 110 134 2 5 55 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 110 134 (Polychromatic418967fa.accept_13_9_6_4_1_2243 9 110 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 110 134 2 4 55 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 110 134 (accept_3_2 7 110 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 110 134 2 3 55 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 110 134 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 110 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 110 134 2 2 55 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 110 134 (Polychromatic418967fa.accept_7_3_5_1_1_72 3
  110 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 110 134 2 1 55 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 110 134 (accept_3_2 1
  110 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110 134))))))))))))))))))))))))) (allB_succ' 26 109 134
  (Eq.refl Bool.true) (allA_of_3_0 26 109 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 108 134 (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 108 134 2 13 54 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 108 134 (accept_3_2 25 108 134 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 108 134 2 12 54 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 108 134 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 108 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 108 134 2 11 54 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 108 134
  (Polychromatic418967fa.accept_19_2_13_1_1_6831 21 108 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 108 134 2 10 54 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 108 134 (accept_3_2 19 108 134 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 108 134 2 9 54 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 108 134 (Polychromatic418967fa.accept_15_2_3_14_1_972 17 108 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 108 134 2 8 54 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 108 134 (Polychromatic418967fa.accept_11_4_9_2_1_259
  15 108 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 108 134 2 7 54 67
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 108 134
  (accept_3_2 13 108 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 134 2 6 54 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 134
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 108 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 108 134 2 5 54 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 108 134 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 108 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 108 134 2 4 54 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 108 134 (accept_3_2 7 108 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 108 134 2 3 54 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 108 134 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 108 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 108 134 2 2 54 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 108 134 (Polychromatic418967fa.accept_20_3_8_14_1_5342
  3 108 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 108 134 2 1 54 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 108 134 (accept_3_2 1
  108 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108 134))))))))))))))))))))))))))) (allB_succ' 28 107 134
  (Eq.refl Bool.true) (allA_succ_of_accept 27 107 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 107 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 107 134
  (Polychromatic418967fa.accept_19_7_12_1_1_6830 26 107 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 107 134 (accept_3_2 25 107 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 107 134 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 107 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 107 134 (Polychromatic418967fa.accept_10_3_7_4_1_584 23 107 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 134 (accept_3_2 22 107 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 107 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 134
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 107 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 107 134 (accept_3_2 19 107 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 107 134 (Polychromatic418967fa.accept_15_3_2_14_1_1713 18 107 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 107 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 107 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 134 (accept_3_2 16 107 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 107 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 134
  (Polychromatic418967fa.accept_13_1_3_4_1_925 14 107 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 107 134 (accept_3_2 13 107 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 107 134 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 107 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 107 134 (Polychromatic418967fa.accept_10_1_7_4_1_968 11 107 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 134 (accept_3_2 10 107 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 107 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 134
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 107 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 107 134 (accept_3_2 7 107 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 134 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 107 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 107 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 134 (accept_3_2 4 107 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 107 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 134
  (Polychromatic418967fa.accept_10_2_7_4_1_967 2 107 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 134 (accept_3_2 1 107 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  134)))))))))))))))))))))))))))) (allB_succ' 29 106 134 (Eq.refl Bool.true) (allA_of_3_0 29 106 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 30 105 134 (Eq.refl Bool.true) (allA_succ_of_accept 29 105 134
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 105 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 105 134 (accept_3_2 28 105 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 105 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 105 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 105 134 (Polychromatic418967fa.accept_10_6_5_4_1_571 26 105 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 134 (accept_3_2 25 105 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 134 (Polychromatic418967fa.accept_26_24_1_4_1_6829 24 105
  134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 105 134
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 105 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 105 134 (accept_3_2 22 105 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 105 134 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 105 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 105 134 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 105 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 134 (accept_3_2 19 105 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 134 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 105 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 134
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 105 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 105 134 (accept_3_2 16 105 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 105 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 105 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 105 134 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 105 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 134 (accept_3_2 13 105 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 134 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 105 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 134
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 105 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 105 134 (accept_3_2 10 105 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  105 134 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 105 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 105 134 (Polychromatic418967fa.accept_20_8_5_14_1_3904 8 105 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 134 (accept_3_2 7 105 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 134 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 105 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 134
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 105 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 105 134 (accept_3_2 4 105 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  105 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 105 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 105 134 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 105 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 134 (accept_3_2 1 105 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 105 134)))))))))))))))))))))))))))))) (allB_succ' 31 104 134 (Eq.refl Bool.true)
  (allA_succ_of_gcd 30 104 134 2 15 52 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 104 134 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 104 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 104 134 2 14 52 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 104 134
  (Polychromatic418967fa.accept_17_10_2_15_1_3179 27 104 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 104 134 2 13 52 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 104 134 (accept_3_2 25 104 134 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 104 134 2 12 52 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 104 134 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 104 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 104 134 2 11 52 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 104 134
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 104 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 104 134 2 10 52 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 104 134 (accept_3_2 19 104 134 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 104 134 2 9 52 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 104 134 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 104 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 104 134 2 8 52 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 104 134 (Polychromatic418967fa.accept_9_6_5_8_1_598 15
  104 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 104 134 2 7 52 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 104 134 (accept_3_2 13
  104 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 104 134 2 6 52 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 104 134
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 104 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 104 134 2 5 52 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 104 134 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 104 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 104 134 2 4 52 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 104 134 (accept_3_2 7 104 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 104 134 2 3 52 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 104 134 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 104 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 104 134 2 2 52 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 104 134 (Polychromatic418967fa.accept_9_3_5_8_1_99 3
  104 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 104 134 2 1 52 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 104 134 (accept_3_2 1
  104 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104 134))))))))))))))))))))))))))))))) (allB_succ' 32 103
  134 (Eq.refl Bool.true) (allA_of_3_0 32 103 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 102 134
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 102 134 2 16 51 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 102 134 (accept_3_2 31 102 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 102 134 2 15 51 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 102 134 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 102 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 102 134 2 14 51 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 102 134
  (Polychromatic418967fa.accept_10_7_2_4_1_569 27 102 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 102 134 2 13 51 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 102 134 (accept_3_2 25 102 134 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 134 2 12 51 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 102 134 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 102 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 102 134 2 11 51 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 102 134
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 102 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 102 134 2 10 51 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 102 134 (accept_3_2 19 102 134 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 134 2 9 51 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 134 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 102 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 102 134 2 8 51 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 102 134 (Polychromatic418967fa.accept_9_6_3_8_1_595 15
  102 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 102 134 2 7 51 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 102 134 (accept_3_2 13
  102 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 134 2 6 51 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 134
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 102 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 102 134 2 5 51 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 102 134 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 102 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 102 134 2 4 51 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 102 134 (accept_3_2 7 102 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 102 134 2 3 51 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 102 134 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 102 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 102 134 2 2 51 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 102 134 (Polychromatic418967fa.accept_7_3_4_1_1_71 3
  102 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 102 134 2 1 51 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 134 (accept_3_2 1
  102 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102 134))))))))))))))))))))))))))))))))) (allB_succ' 34 101
  134 (Eq.refl Bool.true) (allA_succ_of_accept 33 101 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 101 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 134
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 101 134 (accept_3_2 31 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 101 134 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 101 134 (Polychromatic418967fa.accept_19_10_6_1_1_6828 29 101 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 134 (accept_3_2 28 101 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 101 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 101 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 134
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 101 134 (accept_3_2 25 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 101 134 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 101 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 101 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 134 (accept_3_2 22 101 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 101 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 134
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 101 134 (accept_3_2 19 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 101 134 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 101 134 (Polychromatic418967fa.accept_10_7_1_4_1_1447 17 101 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 134 (accept_3_2 16 101 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 101 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 134
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 101 134 (accept_3_2 13 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 101 134 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 101 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 101 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 134 (accept_3_2 10 101 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 101 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 134
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 134 (accept_3_2 7 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 134 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 134 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 101 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 134 (accept_3_2 4 101 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 101 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 134
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 134 (accept_3_2 1 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  134)))))))))))))))))))))))))))))))))) (allB_succ' 35 100 134 (Eq.refl Bool.true) (allA_of_3_0 35 100 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 99 134 (Eq.refl Bool.true) (allA_succ_of_accept 35 99 134
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 99 134 (accept_3_2 34 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  99 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 99 134 (Polychromatic418967fa.accept_27_5_18_26_1_6827 32 99 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 134 (accept_3_2 31 99 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 99 134 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 99 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 134
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 99 134 (accept_3_2 28 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  99 134 (Polychromatic418967fa.accept_15_12_9_14_1_2635 27 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 99 134 (Polychromatic418967fa.accept_19_7_4_1_1_5399 26 99 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 134 (accept_3_2 25 99 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 99 134 (Polychromatic418967fa.accept_13_11_8_4_1_3950 24 99 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 134
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 99 134 (accept_3_2 22 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  99 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 99 134 (Polychromatic418967fa.accept_15_5_9_14_1_1724 20 99 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 134 (accept_3_2 19 99 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 99 134 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 99 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 134
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 99 134 (accept_3_2 16 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  99 134 (Polychromatic418967fa.accept_10_5_9_4_1_1420 15 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 99 134 (Polychromatic418967fa.accept_21_14_15_8_1_5281 14 99 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 134 (accept_3_2 13 99 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 99 134 (Polychromatic418967fa.accept_13_12_8_4_1_3099 12 99
  134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 134
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 99 134 (accept_3_2 10 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  99 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 99 134 (Polychromatic418967fa.accept_10_8_9_4_1_961 8 99 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 134 (accept_3_2 7 99 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 99 134 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 99 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 99
  134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 134 (accept_3_2 4 99 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 134 (Polychromatic418967fa.accept_10_3_9_4_1_960 3
  99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 134
  (Polychromatic418967fa.accept_14_2_1_8_1_650 2 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 99 134 (accept_3_2 1 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  134)))))))))))))))))))))))))))))))))))) (allB_succ' 37 98 134 (Eq.refl Bool.true) (allA_succ_of_gcd 36 98 134 2 18 49
  67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 98 134
  (Polychromatic418967fa.accept_13_9_7_4_1_953 35 98 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 98 134 2 17 49 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 98 134 (Polychromatic418967fa.accept_16_1_2_6_1_2295 33 98 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 98 134 2 16 49 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 98 134 (accept_3_2 31 98 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 98 134 2 15 49 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 98 134 (Polychromatic418967fa.accept_10_9_8_4_1_970 29 98 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 98 134 2 14 49 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 98 134
  (Polychromatic418967fa.accept_16_11_2_6_1_1435 27 98 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 98 134 2 13 49 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 98 134 (accept_3_2 25 98 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 98
  134 2 12 49 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  98 134 (Polychromatic418967fa.accept_11_1_10_2_1_58 23 98 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 98 134 2 11 49 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 98 134 (Polychromatic418967fa.accept_15_6_8_14_1_4575 21 98 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 98 134 2 10 49 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 98 134 (accept_3_2 19 98 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 98 134 2 9 49 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 98 134 (Polychromatic418967fa.accept_16_1_2_6_1_2295
  17 98 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 98 134 2 8 49 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 98 134
  (Polychromatic418967fa.accept_21_15_14_8_1_6826 15 98 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 98 134 2 7 49 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 98 134 (accept_3_2 13 98 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 98
  134 2 6 49 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  98 134 (Polychromatic418967fa.accept_13_11_7_4_1_1561 11 98 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 98 134 2 5 49 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 98 134 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 98 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 98 134 2 4 49 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 98 134 (accept_3_2 7 98 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 98 134 2 3 49 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 98 134 (Polychromatic418967fa.accept_15_5_8_14_1_432 5 98 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 98 134 2 2 49 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 98 134
  (Polychromatic418967fa.accept_13_3_7_4_1_435 3 98 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 98 134 2 1 49 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 98 134 (accept_3_2 1 98 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  134))))))))))))))))))))))))))))))))))))) (allB_succ' 38 97 134 (Eq.refl Bool.true) (allA_of_3_0 38 97 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 96 134 (Eq.refl Bool.true) (allA_succ_of_gcd 38 96 134 2 19 48 67
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 96 134
  (accept_3_2 37 96 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 134 2 18 48 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 96 134
  (Polychromatic418967fa.accept_10_5_6_4_1_64 35 96 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 96 134 2 17 48 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 96 134 (Polychromatic418967fa.accept_17_16_11_15_1_4353 33 96 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 96 134 2 16 48 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 96 134 (accept_3_2 31 96 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96 134 2 15 48 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 96 134 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 96 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 96 134 2 14 48 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 96 134
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 96 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 96 134 2 13 48 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 96 134 (accept_3_2 25 96 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96
  134 2 12 48 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  96 134 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 96 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 96 134 2 11 48 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 96 134 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 96 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 96 134 2 10 48 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 96 134 (accept_3_2 19 96 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 134 2 9 48 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 134 (Polychromatic418967fa.accept_7_3_5_1_1_72 17
  96 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 96 134 2 8 48 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 96 134
  (Polychromatic418967fa.accept_10_5_6_4_1_64 15 96 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 96 134 2 7 48 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 96 134 (accept_3_2 13 96 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96
  134 2 6 48 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  96 134 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 96 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 96 134 2 5 48 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 96 134 (Polychromatic418967fa.accept_13_9_5_4_1_1591 9 96 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 96 134 2 4 48 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 96 134 (accept_3_2 7 96 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 134 2 3 48 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 96 134 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 96 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 134 2 2 48 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 96 134
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 96 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 96 134 2 1 48 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 96 134 (accept_3_2 1 96 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  134))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 95 134 (Eq.refl Bool.true) (allA_succ_of_accept 39 95 134
  (Polychromatic418967fa.accept_6_3_5_2_1_12 39 95 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 95 134 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 95 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 134 (accept_3_2 37 95 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 95 134 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 95 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 134 (Polychromatic418967fa.accept_18_17_5_8_1_1898
  35 95 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 95 134 (accept_3_2 34
  95 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 95 134
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 95 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 95 134 (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 95 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 134 (accept_3_2 31 95 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 95 134 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 95 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 29
  95 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 95 134 (accept_3_2 28 95
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 95 134 (Polychromatic418967fa.accept_6_3_5_2_1_12
  27 95 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 95 134
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 95 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 95 134 (accept_3_2 25 95 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  95 134 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 95 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 95 134 (Polychromatic418967fa.accept_15_8_5_14_1_986 23 95 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 95 134 (accept_3_2 22 95 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 95 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 95 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 95 134
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 95 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 95 134 (accept_3_2 19 95 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  95 134 (Polychromatic418967fa.accept_14_4_11_8_1_2034 18 95 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 95 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 95 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 95 134 (accept_3_2 16 95 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 95 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 95 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 95 134
  (Polychromatic418967fa.accept_18_14_5_8_1_1880 14 95 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 95 134 (accept_3_2 13 95 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  95 134 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 95 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 95 134 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 95 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 95 134 (accept_3_2 10 95 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 95 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 95 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 95 134
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 95 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 95 134 (accept_3_2 7 95 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95
  134 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 95 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 95 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 95 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 95 134 (accept_3_2 4 95 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 95 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 95 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 134 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 95
  134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 134 (accept_3_2 1 95 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95 134)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 94
  134 (Eq.refl Bool.true) (allA_of_3_0 41 94 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 93 134 (Eq.refl
  Bool.true) (allA_succ_of_accept 41 93 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 93 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 134 (accept_3_2 40 93 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 93 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 134
  (Polychromatic418967fa.accept_7_3_2_1_1_225 38 93 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 93 134 (accept_3_2 37 93 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  93 134 (Polychromatic418967fa.accept_16_4_13_6_1_4417 36 93 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 93 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 93 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 134 (accept_3_2 34 93 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 134 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 93 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 134
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 93 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 134 (accept_3_2 31 93 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  93 134 (Polychromatic418967fa.accept_11_8_5_2_1_1629 30 93 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 93 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 93 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 134 (accept_3_2 28 93 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 93 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 134
  (Polychromatic418967fa.accept_15_11_3_14_1_971 26 93 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 134 (accept_3_2 25 93 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  93 134 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 93 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 93 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 93 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 134 (accept_3_2 22 93 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 134 (Polychromatic418967fa.accept_20_1_13_14_1_1481 21 93 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 134
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 93 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 134 (accept_3_2 19 93 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  93 134 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 93 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 93 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 93 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 134 (accept_3_2 16 93 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 93 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 134
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 93 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 134 (accept_3_2 13 93 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  93 134 (Polychromatic418967fa.accept_13_12_2_4_1_3131 12 93 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 93 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 93 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 134 (accept_3_2 10 93 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 134 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 93 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 134
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 8 93 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 134 (accept_3_2 7 93 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93
  134 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 93 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 93 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 134 (accept_3_2 4 93 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 93 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 134 (Polychromatic418967fa.accept_9_2_3_8_1_318 2
  93 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 134 (accept_3_2 1 93 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93 134)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 92
  134 (Eq.refl Bool.true) (allA_succ_of_gcd 42 92 134 2 21 46 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 92 134 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 92 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 92 134 2 20 46 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 92 134
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 92 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 92 134 2 19 46 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 92 134 (accept_3_2 37 92 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 92
  134 2 18 46 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  92 134 (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 92 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 92 134 2 17 46 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 92 134 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 92 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 92 134 2 16 46 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 92 134 (accept_3_2 31 92 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 92 134 2 15 46 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 92 134
  (Polychromatic418967fa.accept_12_5_8_2_1_309 29 92 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 92 134 2 14 46 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 92 134 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 92 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 92 134 2 13 46 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 92 134 (accept_3_2 25 92 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 92 134 2 12 46 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 92 134 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 92 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 92 134 2 11 46 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 92 134
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 92 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 92 134 2 10 46 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 92 134 (accept_3_2 19 92 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 92
  134 2 9 46 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  92 134 (Polychromatic418967fa.accept_10_7_2_4_1_569 17 92 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 92 134 2 8 46 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 92 134 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 92 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 92 134 2 7 46 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 92 134 (accept_3_2 13 92 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 92 134 2 6 46 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 92 134 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 92 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 92 134 2 5 46 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 92 134
  (Polychromatic418967fa.accept_11_9_4_2_1_600 9 92 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 92 134 2 4 46 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 92 134 (accept_3_2 7 92 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 92 134
  2 3 46 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 92
  134 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 92 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 92 134 2 2 46 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 92 134 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 92 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 92 134 2 1 46 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 92 134 (accept_3_2 1 92 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 92 134))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 91 134 (Eq.refl Bool.true)
  (allA_of_3_0 44 91 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 90 134 (Eq.refl Bool.true)
  (allA_succ_of_gcd 44 90 134 2 22 45 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 90 134 (accept_3_2 43 90 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 90
  134 2 21 45 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  90 134 (Polychromatic418967fa.accept_13_2_12_4_1_943 41 90 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 90 134 2 20 45 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 90 134 (Polychromatic418967fa.accept_12_3_6_2_1_747 39 90 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 90 134 2 19 45 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 90 134 (accept_3_2 37 90 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 90 134 2 18 45 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 90 134
  (Polychromatic418967fa.accept_14_7_6_8_1_2856 35 90 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 90 134 2 17 45 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 90 134 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 90 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 90 134 2 16 45 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 90 134 (accept_3_2 31 90 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 134 2 15 45 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 134 (Polychromatic418967fa.accept_13_3_12_4_1_110 29 90 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 90 134 2 14 45 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 90 134
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 90 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 90 134 2 13 45 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 90 134 (accept_3_2 25 90 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 90
  134 2 12 45 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  90 134 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 90 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 90 134 2 11 45 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 90 134 (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 90 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 90 134 2 10 45 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 134 (accept_3_2 19 90 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90 134 2 9 45 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 90 134 (Polychromatic418967fa.accept_19_17_14_1_1_6825
  17 90 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 134 2 8 45 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 90 134
  (Polychromatic418967fa.accept_12_3_6_2_1_747 15 90 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 90 134 2 7 45 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 90 134 (accept_3_2 13 90 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90
  134 2 6 45 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  90 134 (Polychromatic418967fa.accept_13_11_12_4_1_3945 11 90 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 90 134 2 5 45 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 90 134 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 90 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 90 134 2 4 45 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 134 (accept_3_2 7 90 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 134 2 3 45 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 90 134 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 90 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 90 134 2 2 45 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 90 134
  (Polychromatic418967fa.accept_12_3_6_2_1_747 3 90 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 90 134 2 1 45 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 90 134 (accept_3_2 1 90 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  134))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 89 134 (Eq.refl Bool.true) (allA_succ_of_accept 45 89
  134 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 89 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 89 134 (Polychromatic418967fa.accept_12_8_5_2_1_746 44 89 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 134 (accept_3_2 43 89 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 89 134 (Polychromatic418967fa.accept_25_17_14_9_1_6824 42 89 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 134
  (Polychromatic418967fa.accept_7_6_5_1_1_416 41 89 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 134 (accept_3_2 40 89 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 89 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 134 (Polychromatic418967fa.accept_7_3_5_1_1_72 38 89 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 134 (accept_3_2 37 89 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 134 (Polychromatic418967fa.accept_11_3_1_2_1_1063 36 89 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 134
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 89 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 134 (accept_3_2 34 89 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 89 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 134 (Polychromatic418967fa.accept_7_4_5_1_1_418 32 89 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 134 (accept_3_2 31 89 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 134 (Polychromatic418967fa.accept_24_6_17_14_1_6823 30 89 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 134
  (Polychromatic418967fa.accept_16_13_9_6_1_2306 29 89 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 134 (accept_3_2 28 89 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 89 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 134 (Polychromatic418967fa.accept_19_7_13_1_1_6804 26 89 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 134 (accept_3_2 25 89 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 134 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 89 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 134
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 89 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 134 (accept_3_2 22 89 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 89 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 134 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 89 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 134 (accept_3_2 19 89 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 134 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 89 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 134
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 89 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 134 (accept_3_2 16 89 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 89 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 134 (Polychromatic418967fa.accept_11_3_1_2_1_1063 14 89 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 134 (accept_3_2 13 89 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 134 (Polychromatic418967fa.accept_13_12_11_4_1_3111 12 89 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 134
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 89 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 134 (accept_3_2 10 89 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 89 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 134 (Polychromatic418967fa.accept_10_8_9_4_1_961 8 89 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 134 (accept_3_2 7 89 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 134 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 89 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 134
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 5 89 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 134 (accept_3_2 4 89 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  134 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 89 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 134 (Polychromatic418967fa.accept_13_2_11_4_1_445 2 89 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 134 (accept_3_2 1 89 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 134)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 88 134 (Eq.refl Bool.true)
  (allA_of_3_0 47 88 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 87 134 (Eq.refl Bool.true)
  (allA_succ_of_accept 47 87 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 87 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 134 (accept_3_2 46 87 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 87 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 87 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 134 (Polychromatic418967fa.accept_7_2_3_1_1_10 44
  87 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 134 (accept_3_2 43 87
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 87 134
  (Polychromatic418967fa.accept_10_2_7_4_1_967 42 87 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 87 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 87 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 134 (accept_3_2 40 87 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 87 134 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 87 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 134 (Polychromatic418967fa.accept_9_2_6_8_1_321 38
  87 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 134 (accept_3_2 37 87
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 87 134
  (Polychromatic418967fa.accept_21_15_3_8_1_6822 36 87 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 87 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 87 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 134 (accept_3_2 34 87 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 87 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 87 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 134 (Polychromatic418967fa.accept_7_4_3_1_1_87 32
  87 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 134 (accept_3_2 31 87
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 87 134 (Polychromatic418967fa.accept_7_2_3_1_1_10
  30 87 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 134
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 87 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 87 134 (accept_3_2 28 87 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  87 134 (Polychromatic418967fa.accept_17_10_2_15_1_3179 27 87 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 87 134 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 87 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 134 (accept_3_2 25 87 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 87 134 (Polychromatic418967fa.accept_15_9_12_14_1_963 24 87 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 134
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 87 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 87 134 (accept_3_2 22 87 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  87 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 87 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 87 134 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 87 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 134 (accept_3_2 19 87 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 87 134 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 87 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 134
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 87 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 87 134 (accept_3_2 16 87 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  87 134 (Polychromatic418967fa.accept_16_15_7_6_1_1453 15 87 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 87 134 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 87 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 134 (accept_3_2 13 87 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 87 134 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 87 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 134
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 87 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 134 (accept_3_2 10 87 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  87 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 87 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 134 (Polychromatic418967fa.accept_13_8_9_4_1_1552 8 87 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 134 (accept_3_2 7 87 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 87 134 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 87 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 87
  134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 134 (accept_3_2 4 87 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 134 (Polychromatic418967fa.accept_9_3_6_8_1_308 3
  87 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 134
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 87 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 87 134 (accept_3_2 1 87 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  134)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 86 134 (Eq.refl Bool.true) (allA_succ_of_gcd 48 86
  134 2 24 43 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  86 134 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 86 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 86 134 2 23 43 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 86 134 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 86 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 86 134 2 22 43 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 86 134 (accept_3_2 43 86 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 86 134 2 21 43 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 86 134
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 86 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 86 134 2 20 43 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 86 134 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 86 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 86 134 2 19 43 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 86 134 (accept_3_2 37 86 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 86 134 2 18 43 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 86 134 (Polychromatic418967fa.accept_10_5_6_4_1_64 35 86 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 86 134 2 17 43 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 86 134
  (Polychromatic418967fa.accept_9_6_5_8_1_598 33 86 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 86 134 2 16 43 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 86 134 (accept_3_2 31 86 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 86
  134 2 15 43 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  86 134 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 86 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 86 134 2 14 43 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 86 134 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 86 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 86 134 2 13 43 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 86 134 (accept_3_2 25 86 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 86 134 2 12 43 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 86 134
  (Polychromatic418967fa.accept_13_10_8_4_1_3098 23 86 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 86 134 2 11 43 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 86 134 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 86 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 86 134 2 10 43 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 86 134 (accept_3_2 19 86 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 86 134 2 9 43 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 86 134 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 86 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 86 134 2 8 43 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 86 134
  (Polychromatic418967fa.accept_9_6_5_8_1_598 15 86 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 86 134 2 7 43 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 86 134 (accept_3_2 13 86 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 86
  134 2 6 43 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  86 134 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 86 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 86 134 2 5 43 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 86 134 (Polychromatic418967fa.accept_13_9_8_4_1_937 9 86 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 86 134 2 4 43 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 86 134 (accept_3_2 7 86 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 86 134 2 3 43 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 86 134 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 86 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 86 134 2 2 43 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 86 134
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 86 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 86 134 2 1 43 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 86 134 (accept_3_2 1 86 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  134))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 85 134 (Eq.refl Bool.true) (allA_of_3_0 50 85 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 84 134 (Eq.refl Bool.true) (allA_succ_of_gcd 50 84 134 2 25 42
  67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 84 134
  (accept_3_2 49 84 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 84 134 2 24 42 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 84 134
  (Polychromatic418967fa.accept_9_2_3_8_1_318 47 84 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 84 134 2 23 42 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 84 134 (Polychromatic418967fa.accept_16_13_4_6_1_2322 45 84 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 84 134 2 22 42 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 84 134 (accept_3_2 43 84 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 134 2 21 42 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 134 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 84 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 84 134 2 20 42 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 84 134
  (Polychromatic418967fa.accept_18_3_12_8_1_5415 39 84 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 84 134 2 19 42 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 84 134 (accept_3_2 37 84 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84
  134 2 18 42 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  84 134 (Polychromatic418967fa.accept_13_9_6_4_1_2243 35 84 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 84 134 2 17 42 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 84 134 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 84 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 84 134 2 16 42 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 84 134 (accept_3_2 31 84 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 134 2 15 42 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 134
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 84 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 84 134 2 14 42 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 84 134 (Polychromatic418967fa.accept_15_12_9_14_1_2635 27 84 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 84 134 2 13 42 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 134 (accept_3_2 25 84 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 134 2 12 42 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 134 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 84 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84 134 2 11 42 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 84 134
  (Polychromatic418967fa.accept_15_6_9_14_1_3457 21 84 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 84 134 2 10 42 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 84 134 (accept_3_2 19 84 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84
  134 2 9 42 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  84 134 (Polychromatic418967fa.accept_31_17_22_10_1_6821 17 84 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 84 134 2 8 42 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 84 134 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 84 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 134 2 7 42 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 134 (accept_3_2 13 84 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 134 2 6 42 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 84 134 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 84 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 134 2 5 42 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 84 134
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 84 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 84 134 2 4 42 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 84 134 (accept_3_2 7 84 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 134
  2 3 42 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84
  134 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 84 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 84 134 2 2 42 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 84 134 (Polychromatic418967fa.accept_16_3_4_6_1_6798 3 84 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 84 134 2 1 42 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 134 (accept_3_2 1 84 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 84 134))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 83 134 (Eq.refl
  Bool.true) (allA_succ_of_accept 51 83 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 83 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 83 134 (Polychromatic418967fa.accept_9_5_2_8_1_109 50
  83 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 134 (accept_3_2 49 83
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 134
  (Polychromatic418967fa.accept_9_3_2_8_1_108 48 83 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 83 134 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 83 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 83 134 (accept_3_2 46 83 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 83 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 83 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 83 134 (Polychromatic418967fa.accept_7_2_6_1_1_73 44
  83 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 134 (accept_3_2 43 83
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 134
  (Polychromatic418967fa.accept_9_6_2_8_1_592 42 83 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 83 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 83 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 83 134 (accept_3_2 40 83 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 83 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 83 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 83 134 (Polychromatic418967fa.accept_13_12_5_4_1_3133
  38 83 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 134 (accept_3_2 37
  83 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 134
  (Polychromatic418967fa.accept_13_10_5_4_1_3107 36 83 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 83 134 (Polychromatic418967fa.accept_13_9_5_4_1_1591 35 83 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 83 134 (accept_3_2 34 83 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 83 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 83 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 83 134 (Polychromatic418967fa.accept_9_5_2_8_1_109 32
  83 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 134 (accept_3_2 31 83
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 134 (Polychromatic418967fa.accept_7_2_6_1_1_73
  30 83 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 134
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 83 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 134 (accept_3_2 28 83 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 83 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 134 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 83 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 134 (accept_3_2 25 83 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 134 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 83 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 134
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 83 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 134 (accept_3_2 22 83 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 83 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 134 (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 83 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 134 (accept_3_2 19 83 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 134 (Polychromatic418967fa.accept_16_2_3_6_1_3372 18 83 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 134
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 83 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 134 (accept_3_2 16 83 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 83 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 134 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 83 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 134 (accept_3_2 13 83 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 134 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 83 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 134
  (Polychromatic418967fa.accept_16_11_3_6_1_4462 11 83 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 134 (accept_3_2 10 83 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 83 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 83 134 (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 83 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 134 (accept_3_2 7 83 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 83 134 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 83 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 83
  134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 83 134 (accept_3_2 4 83 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 83
  134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 134
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 83 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 83 134 (accept_3_2 1 83 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 83
  134)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 82 134 (Eq.refl Bool.true) (allA_of_3_0 53 82
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 81 134 (Eq.refl Bool.true) (allA_succ_of_accept 53 81 134
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 81 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 81 134 (accept_3_2 52 81 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  81 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 81 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 81 134 (Polychromatic418967fa.accept_11_6_4_2_1_599 50 81 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 134 (accept_3_2 49 81 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 81 134 (Polychromatic418967fa.accept_28_20_25_22_1_6820 48 81 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 134
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 81 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 81 134 (accept_3_2 46 81 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  81 134 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 81 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 81 134 (Polychromatic418967fa.accept_19_6_5_1_1_2765 44 81 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 134 (accept_3_2 43 81 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 81 134 (Polychromatic418967fa.accept_11_9_4_2_1_600 42 81 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 134
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 81 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 134 (accept_3_2 40 81 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  81 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 81 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 81 134 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 81 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 134 (accept_3_2 37 81 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 81 134 (Polychromatic418967fa.accept_17_2_13_15_1_4349 36 81 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 134
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 81 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 81 134 (accept_3_2 34 81 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  81 134 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 81 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 81 134 (Polychromatic418967fa.accept_14_4_11_8_1_2034 32 81 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 134 (accept_3_2 31 81 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 81 134 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 81 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 134
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 81 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 81 134 (accept_3_2 28 81 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  81 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 81 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 81 134 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 81 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 134 (accept_3_2 25 81 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 134 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 81 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 134
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 81 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 134 (accept_3_2 22 81 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  81 134 (Polychromatic418967fa.accept_16_5_1_6_1_3367 21 81 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 81 134 (Polychromatic418967fa.accept_11_9_4_2_1_600 20 81 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 134 (accept_3_2 19 81 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 134 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 81 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 134
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 81 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 81 134 (accept_3_2 16 81 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  81 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 81 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 81 134 (Polychromatic418967fa.accept_13_1_3_4_1_925 14 81 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 134 (accept_3_2 13 81 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 134 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 81 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 134
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 81 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 134 (accept_3_2 10 81 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  81 134 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 81 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 81 134 (Polychromatic418967fa.accept_15_8_6_14_1_975 8 81 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 134 (accept_3_2 7 81 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 134 (Polychromatic418967fa.accept_11_6_4_2_1_599 6 81 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 134
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 81 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 134 (accept_3_2 4 81 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81
  134 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 81 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 134 (Polychromatic418967fa.accept_16_2_1_6_1_2342 2 81 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 134 (accept_3_2 1 81 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 81 134)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 80 134 (Eq.refl
  Bool.true) (allA_succ_of_gcd 54 80 134 2 27 40 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 80 134 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 80 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 80 134 2 26 40 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 80 134
  (Polychromatic418967fa.accept_7_2_3_1_1_10 51 80 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 80 134 2 25 40 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 80 134 (accept_3_2 49 80 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 80
  134 2 24 40 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  80 134 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 80 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 80 134 2 23 40 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 80 134 (Polychromatic418967fa.accept_11_1_3_2_1_1090 45 80 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 80 134 2 22 40 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 80 134 (accept_3_2 43 80 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 80 134 2 21 40 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 80 134
  (Polychromatic418967fa.accept_12_5_8_2_1_309 41 80 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 80 134 2 20 40 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 80 134 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 80 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 80 134 2 19 40 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 80 134 (accept_3_2 37 80 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 80 134 2 18 40 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 80 134 (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 80 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 80 134 2 17 40 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 80 134
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 80 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 80 134 2 16 40 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 80 134 (accept_3_2 31 80 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80
  134 2 15 40 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  80 134 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 80 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 80 134 2 14 40 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 80 134 (Polychromatic418967fa.accept_25_2_5_9_1_6819 27 80 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 80 134 2 13 40 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 80 134 (accept_3_2 25 80 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 80 134 2 12 40 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 80 134
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 80 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 80 134 2 11 40 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 80 134 (Polychromatic418967fa.accept_15_6_5_14_1_429 21 80 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 80 134 2 10 40 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 80 134 (accept_3_2 19 80 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 80 134 2 9 40 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 80 134 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 80 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 80 134 2 8 40 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 80 134
  (Polychromatic418967fa.accept_19_15_4_1_1_4060 15 80 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 80 134 2 7 40 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 80 134 (accept_3_2 13 80 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80
  134 2 6 40 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  80 134 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 80 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 80 134 2 5 40 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 80 134 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 80 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 80 134 2 4 40 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 80 134 (accept_3_2 7 80 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 80 134 2 3 40 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 80 134 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 80 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 80 134 2 2 40 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 80 134
  (Polychromatic418967fa.accept_17_3_12_15_1_1203 3 80 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 80 134 2 1 40 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 80 134 (accept_3_2 1 80 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  134))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 79 134 (Eq.refl Bool.true) (allA_of_3_0 56
  79 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 78 134 (Eq.refl Bool.true) (allA_succ_of_gcd 56 78 134
  2 28 39 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 78
  134 (accept_3_2 55 78 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 78 134 2 27 39 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 78 134
  (Polychromatic418967fa.accept_17_2_10_15_1_1238 53 78 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 78 134 2 26 39 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 78 134 (Polychromatic418967fa.accept_12_3_6_2_1_747 51 78 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 78 134 2 25 39 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 78 134 (accept_3_2 49 78 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 78 134 2 24 39 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 78 134 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 78 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 78 134 2 23 39 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 78 134
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 45 78 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 78 134 2 22 39 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 78 134 (accept_3_2 43 78 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 78
  134 2 21 39 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  78 134 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 78 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 78 134 2 20 39 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 78 134 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 78 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 78 134 2 19 39 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 78 134 (accept_3_2 37 78 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 134 2 18 39 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 134
  (Polychromatic418967fa.accept_21_14_15_8_1_5281 35 78 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 78 134 2 17 39 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 78 134 (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 78 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 78 134 2 16 39 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 78 134 (accept_3_2 31 78 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 134 2 15 39 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 134 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 78 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 78 134 2 14 39 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 78 134
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 78 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 78 134 2 13 39 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 78 134 (accept_3_2 25 78 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78
  134 2 12 39 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  78 134 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 78 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 78 134 2 11 39 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 78 134 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 78 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 78 134 2 10 39 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 78 134 (accept_3_2 19 78 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 134 2 9 39 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 134 (Polychromatic418967fa.accept_15_2_3_14_1_972
  17 78 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 134 2 8 39 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 78 134
  (Polychromatic418967fa.accept_12_3_6_2_1_747 15 78 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 78 134 2 7 39 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 78 134 (accept_3_2 13 78 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78
  134 2 6 39 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  78 134 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 78 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 78 134 2 5 39 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 78 134 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 78 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 78 134 2 4 39 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 78 134 (accept_3_2 7 78 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 134 2 3 39 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 78 134 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 78 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 134 2 2 39 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 78 134
  (Polychromatic418967fa.accept_9_3_6_8_1_308 3 78 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 78 134 2 1 39 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 78 134 (accept_3_2 1 78 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  134))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 77 134 (Eq.refl Bool.true)
  (allA_succ_of_accept 57 77 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 77 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 77 134 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 77 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 134 (accept_3_2 55 77 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 134 (Polychromatic418967fa.accept_13_2_12_4_1_943
  54 77 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 134
  (Polychromatic418967fa.accept_10_3_7_4_1_584 53 77 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 134 (accept_3_2 52 77 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 77 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 134 (Polychromatic418967fa.accept_13_11_12_4_1_3945 50 77 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 134 (accept_3_2 49 77 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 134 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 77 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 134
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 77 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 134 (accept_3_2 46 77 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 77 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 134 (Polychromatic418967fa.accept_12_8_5_2_1_746 44 77 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 134 (accept_3_2 43 77 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 134 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 77 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 134
  (Polychromatic418967fa.accept_10_1_7_4_1_968 41 77 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 134 (accept_3_2 40 77 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 77 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 134 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 77 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 134 (accept_3_2 37 77 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 134 (Polychromatic418967fa.accept_16_4_13_6_1_4417 36 77 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 134
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 77 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 134 (accept_3_2 34 77 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 77 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 134 (Polychromatic418967fa.accept_10_2_7_4_1_967 32 77 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 134 (accept_3_2 31 77 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 134 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 77 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 134
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 77 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 134 (accept_3_2 28 77 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 77 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 134 (Polychromatic418967fa.accept_21_5_14_8_1_6818 26 77 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 134 (accept_3_2 25 77 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 134 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 77 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 134
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 77 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 134 (accept_3_2 22 77 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 77 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 134 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 77 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 134 (accept_3_2 19 77 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 134 (Polychromatic418967fa.accept_13_5_12_4_1_449 18 77 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 134
  (Polychromatic418967fa.accept_18_17_5_8_1_1898 17 77 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 134 (accept_3_2 16 77 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 77 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 134 (Polychromatic418967fa.accept_18_14_5_8_1_1880 14 77 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 134 (accept_3_2 13 77 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 134 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 77 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 134
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 77 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 134 (accept_3_2 10 77 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 77 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 134 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 77 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 134 (accept_3_2 7 77 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 134 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 77 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 134
  (Polychromatic418967fa.accept_13_5_12_4_1_449 5 77 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 134 (accept_3_2 4 77 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  134 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 77 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 134 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 77 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 134 (accept_3_2 1 77 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 134)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 76 134 (Eq.refl
  Bool.true) (allA_of_3_0 59 76 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 75 134 (Eq.refl Bool.true)
  (allA_succ_of_accept 59 75 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 75 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 134 (accept_3_2 58 75 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 75 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 75 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 134 (Polychromatic418967fa.accept_9_2_3_8_1_318 56
  75 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 134 (accept_3_2 55 75
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 75 134
  (Polychromatic418967fa.accept_12_6_3_2_1_743 54 75 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 75 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 75 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 134 (accept_3_2 52 75 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 75 134 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 75 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 134 (Polychromatic418967fa.accept_9_5_3_8_1_316 50
  75 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 134 (accept_3_2 49 75
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 75 134
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 75 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 75 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 75 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 134 (accept_3_2 46 75 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 75 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 75 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 134 (Polychromatic418967fa.accept_13_5_10_4_1_1564
  44 75 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 134 (accept_3_2 43
  75 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 75 134
  (Polychromatic418967fa.accept_9_6_3_8_1_595 42 75 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 75 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 75 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 134 (accept_3_2 40 75 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 75 134 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 75 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 134 (Polychromatic418967fa.accept_7_3_5_1_1_72 38
  75 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 134 (accept_3_2 37 75
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 75 134
  (Polychromatic418967fa.accept_10_6_5_4_1_571 36 75 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 75 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 75 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 134 (accept_3_2 34 75 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 75 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 75 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 134 (Polychromatic418967fa.accept_7_4_5_1_1_418 32
  75 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 134 (accept_3_2 31 75
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 75 134
  (Polychromatic418967fa.accept_12_6_3_2_1_743 30 75 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 75 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 75 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 134 (accept_3_2 28 75 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 75 134 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 75 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 134 (Polychromatic418967fa.accept_10_6_5_4_1_571
  26 75 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 134 (accept_3_2 25
  75 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 75 134
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 75 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 75 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 75 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 134 (accept_3_2 22 75 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 75 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 75 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 134 (Polychromatic418967fa.accept_7_6_5_1_1_416 20
  75 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 134 (accept_3_2 19 75
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 134
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 75 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 75 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 75 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 134 (accept_3_2 16 75 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 75 134 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 75 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 134 (Polychromatic418967fa.accept_9_5_3_8_1_316 14
  75 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 134 (accept_3_2 13 75
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 75 134
  (Polychromatic418967fa.accept_18_12_3_8_1_6817 12 75 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 75 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 75 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 134 (accept_3_2 10 75 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 75 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 75 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 134 (Polychromatic418967fa.accept_13_8_10_4_1_2270
  8 75 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 134 (accept_3_2 7 75
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 134 (Polychromatic418967fa.accept_7_6_5_1_1_416
  6 75 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 75 134
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 75 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 75 134 (accept_3_2 4 75 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75
  134 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 75 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 75 134 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 75 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 134 (accept_3_2 1 75 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 75 134)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 74 134
  (Eq.refl Bool.true) (allA_succ_of_gcd 60 74 134 2 30 37 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 74 134 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 74 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 74 134 2 29 37 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 74 134
  (Polychromatic418967fa.accept_9_3_2_8_1_108 57 74 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 74 134 2 28 37 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 74 134 (accept_3_2 55 74 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 74
  134 2 27 37 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  74 134 (Polychromatic418967fa.accept_14_11_4_8_1_664 53 74 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 74 134 2 26 37 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 74 134 (Polychromatic418967fa.accept_9_6_2_8_1_592 51 74 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 74 134 2 25 37 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 74 134 (accept_3_2 49 74 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 74 134 2 24 37 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 74 134
  (Polychromatic418967fa.accept_7_5_4_1_1_412 47 74 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 74 134 2 23 37 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 74 134 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 74 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 74 134 2 22 37 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 74 134 (accept_3_2 43 74 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 74 134 2 21 37 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 74 134 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 74 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 74 134 2 20 37 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 74 134
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 74 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 74 134 2 19 37 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 74 134 (accept_3_2 37 74 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 74
  134 2 18 37 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  74 134 (Polychromatic418967fa.accept_18_17_2_8_1_6800 35 74 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 74 134 2 17 37 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 74 134 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 74 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 74 134 2 16 37 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 74 134 (accept_3_2 31 74 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 74 134 2 15 37 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 74 134
  (Polychromatic418967fa.accept_19_10_17_1_1_4010 29 74 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 74 134 2 14 37 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 74 134 (Polychromatic418967fa.accept_11_5_8_2_1_588 27 74 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 74 134 2 13 37 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 74 134 (accept_3_2 25 74 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 74 134 2 12 37 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 74 134 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 74 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 74 134 2 11 37 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 74 134
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 74 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 74 134 2 10 37 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 74 134 (accept_3_2 19 74 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 74
  134 2 9 37 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  74 134 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 74 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 74 134 2 8 37 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 74 134 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 74 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 74 134 2 7 37 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 74 134 (accept_3_2 13 74 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74 134 2 6 37 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 74 134 (Polychromatic418967fa.accept_14_11_4_8_1_664 11 74 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 74 134 2 5 37 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 74 134
  (Polychromatic418967fa.accept_17_9_6_15_1_5454 9 74 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 74 134 2 4 37 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 74 134 (accept_3_2 7 74 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 74 134
  2 3 37 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 74
  134 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 74 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 74 134 2 2 37 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 74 134 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 74 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 74 134 2 1 37 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 74 134 (accept_3_2 1 74 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 74 134))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 73 134
  (Eq.refl Bool.true) (allA_of_3_0 62 73 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 72 134 (Eq.refl
  Bool.true) (allA_succ_of_gcd 62 72 134 2 31 36 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 72 134 (accept_3_2 61 72 134 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 72 134 2 30 36 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 72 134 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 72 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 72 134 2 29 36 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 72 134 (Polychromatic418967fa.accept_10_7_2_4_1_569 57
  72 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 72 134 2 28 36 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 72 134 (accept_3_2 55
  72 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 72 134 2 27 36 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 72 134
  (Polychromatic418967fa.accept_17_2_4_15_1_5451 53 72 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 72 134 2 26 36 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 72 134 (Polychromatic418967fa.accept_13_12_7_4_1_3124 51 72 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 72 134 2 25 36 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 72 134 (accept_3_2 49 72 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 134 2 24 36 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 134 (Polychromatic418967fa.accept_10_7_2_4_1_569 47 72 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 72 134 2 23 36 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 72 134
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 72 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 72 134 2 22 36 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 72 134 (accept_3_2 43 72 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72
  134 2 21 36 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  72 134 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 72 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 72 134 2 20 36 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 72 134 (Polychromatic418967fa.accept_15_9_12_14_1_963 39 72 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 72 134 2 19 36 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 134 (accept_3_2 37 72 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 134 2 18 36 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 134
  (Polychromatic418967fa.accept_13_9_7_4_1_953 35 72 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 72 134 2 17 36 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 72 134 (Polychromatic418967fa.accept_17_16_4_15_1_4342 33 72 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 72 134 2 16 36 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 72 134 (accept_3_2 31 72 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 134 2 15 36 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 134 (Polychromatic418967fa.accept_13_3_7_4_1_435 29 72 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 72 134 2 14 36 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 72 134
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 72 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 72 134 2 13 36 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 72 134 (accept_3_2 25 72 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72
  134 2 12 36 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  72 134 (Polychromatic418967fa.accept_13_10_7_4_1_2262 23 72 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 72 134 2 11 36 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 72 134 (Polychromatic418967fa.accept_19_2_15_1_1_3977 21 72 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 72 134 2 10 36 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 72 134 (accept_3_2 19 72 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72 134 2 9 36 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 72 134 (Polychromatic418967fa.accept_7_3_2_1_1_225 17
  72 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72 134 2 8 36 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 72 134
  (Polychromatic418967fa.accept_11_4_6_2_1_51 15 72 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 72 134 2 7 36 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 72 134 (accept_3_2 13 72 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72
  134 2 6 36 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  72 134 (Polychromatic418967fa.accept_13_11_7_4_1_1561 11 72 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 72 134 2 5 36 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 72 134 (Polychromatic418967fa.accept_13_9_7_4_1_953 9 72 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 72 134 2 4 36 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 72 134 (accept_3_2 7 72 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 134 2 3 36 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 72 134 (Polychromatic418967fa.accept_19_5_15_1_1_4041 5 72 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 134 2 2 36 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 72 134
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 72 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 72 134 2 1 36 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 72 134 (accept_3_2 1 72 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  134))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 71 134 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 71 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 71 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 71 134 (Polychromatic418967fa.accept_13_10_6_4_1_1583 62 71
  134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 134 (accept_3_2 61 71 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 134
  (Polychromatic418967fa.accept_25_10_21_9_1_6816 60 71 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 71 134 (Polychromatic418967fa.accept_13_7_6_4_1_933 59 71 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 71 134 (accept_3_2 58 71 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 71 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 71 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 71 134 (Polychromatic418967fa.accept_12_8_11_2_1_1277
  56 71 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 134 (accept_3_2 55
  71 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 134
  (Polychromatic418967fa.accept_13_2_6_4_1_1593 54 71 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 71 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 71 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 71 134 (accept_3_2 52 71 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 71 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 71 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 71 134 (Polychromatic418967fa.accept_13_11_6_4_1_3121
  50 71 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 134 (accept_3_2 49
  71 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 134
  (Polychromatic418967fa.accept_13_9_6_4_1_2243 48 71 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 71 134 (Polychromatic418967fa.accept_10_7_1_4_1_1447 47 71 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 71 134 (accept_3_2 46 71 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 71 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 71 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 71 134 (Polychromatic418967fa.accept_12_8_11_2_1_1277
  44 71 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 134 (accept_3_2 43
  71 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 134
  (Polychromatic418967fa.accept_15_12_11_14_1_3464 42 71 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 71 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 71 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 71 134 (accept_3_2 40 71 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 71 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 71 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 71 134
  (Polychromatic418967fa.accept_18_2_17_8_1_1893 38 71 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 71 134 (accept_3_2 37 71 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  71 134 (Polychromatic418967fa.accept_13_10_6_4_1_1583 36 71 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 71 134 (Polychromatic418967fa.accept_10_5_1_4_1_1444 35 71 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 71 134 (accept_3_2 34 71 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 71 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 71 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 71 134
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 71 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 71 134 (accept_3_2 31 71 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  71 134 (Polychromatic418967fa.accept_11_8_5_2_1_1629 30 71 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 71 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 71 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 71 134 (accept_3_2 28 71 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 71 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 71 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 71 134
  (Polychromatic418967fa.accept_20_6_11_14_1_5343 26 71 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 71 134 (accept_3_2 25 71 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  71 134 (Polychromatic418967fa.accept_13_11_6_4_1_3121 24 71 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 71 134 (Polychromatic418967fa.accept_13_10_6_4_1_1583 23 71 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 71 134 (accept_3_2 22 71 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 71 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 71 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 71 134
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 71 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 71 134 (accept_3_2 19 71 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  71 134 (Polychromatic418967fa.accept_13_5_6_4_1_1582 18 71 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 71 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 71 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 71 134 (accept_3_2 16 71 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 71 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 71 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 71 134
  (Polychromatic418967fa.accept_17_14_3_15_1_5449 14 71 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 71 134 (accept_3_2 13 71 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  71 134 (Polychromatic418967fa.accept_15_12_11_14_1_3464 12 71 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 71 134 (Polychromatic418967fa.accept_13_11_6_4_1_3121 11 71 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 71 134 (accept_3_2 10 71 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 71 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 71 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 134
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 8 71 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 71 134 (accept_3_2 7 71 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71
  134 (Polychromatic418967fa.accept_19_6_14_1_1_2752 6 71 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 71 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 71 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 71 134 (accept_3_2 4 71 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 71 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 71 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 134
  (Polychromatic418967fa.accept_13_2_6_4_1_1593 2 71 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 71 134 (accept_3_2 1 71 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 71
  134)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 70 134 (Eq.refl Bool.true)
  (allA_of_3_0 65 70 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 69 134 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 69 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 69 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 134 (accept_3_2 64 69 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 69 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 69 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 134 (Polychromatic418967fa.accept_19_5_12_1_1_2817
  62 69 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 134 (accept_3_2 61
  69 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 69 134
  (Polychromatic418967fa.accept_17_9_1_15_1_3156 60 69 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 69 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 69 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 134 (accept_3_2 58 69 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 69 134 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 69 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 134 (Polychromatic418967fa.accept_9_2_6_8_1_321 56
  69 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 69 134 (accept_3_2 55 69
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 69 134
  (Polychromatic418967fa.accept_7_5_6_1_1_407 54 69 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 69 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 69 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 134 (accept_3_2 52 69 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 69 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 69 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 134 (Polychromatic418967fa.accept_9_5_6_8_1_101 50
  69 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 134 (accept_3_2 49 69
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 69 134
  (Polychromatic418967fa.accept_9_3_6_8_1_308 48 69 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 69 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 69 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 134 (accept_3_2 46 69 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 69 134 (Polychromatic418967fa.accept_10_5_9_4_1_1420 45 69 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 134 (Polychromatic418967fa.accept_7_2_6_1_1_73 44
  69 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 134 (accept_3_2 43 69
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 69 134
  (Polychromatic418967fa.accept_12_6_9_2_1_311 42 69 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 69 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 69 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 134 (accept_3_2 40 69 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 69 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 69 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 134 (Polychromatic418967fa.accept_9_2_6_8_1_321 38
  69 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 134 (accept_3_2 37 69
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 69 134
  (Polychromatic418967fa.accept_15_6_9_14_1_3457 36 69 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 69 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 69 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 134 (accept_3_2 34 69 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 69 134 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 69 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 134 (Polychromatic418967fa.accept_9_5_6_8_1_101 32
  69 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 134 (accept_3_2 31 69
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 69 134 (Polychromatic418967fa.accept_7_2_6_1_1_73
  30 69 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 134
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 69 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 69 134 (accept_3_2 28 69 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  69 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 69 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 69 134 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 69 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 134 (accept_3_2 25 69 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 69 134 (Polychromatic418967fa.accept_19_5_12_1_1_2817 24 69 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 134
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 69 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 69 134 (accept_3_2 22 69 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  69 134 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 69 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 69 134 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 69 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 134 (accept_3_2 19 69 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 69 134 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 69 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 134
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 69 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 69 134 (accept_3_2 16 69 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  69 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 69 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 69 134 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 69 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 134 (accept_3_2 13 69 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 69 134 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 69 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 134
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 69 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 134 (accept_3_2 10 69 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  69 134 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 69 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 69 134 (Polychromatic418967fa.accept_10_8_9_4_1_961 8 69 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 134 (accept_3_2 7 69 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 69 134 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 69 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 134
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 69 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 69 134 (accept_3_2 4 69 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69
  134 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 69 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 69 134 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 69 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 134 (accept_3_2 1 69 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 69 134)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 68 134
  (Eq.refl Bool.true) (allA_succ_of_gcd 66 68 134 2 33 34 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 68 134 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 68 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 68 134 2 32 34 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 68 134
  (Polychromatic418967fa.accept_19_6_11_1_1_6815 63 68 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 68 134 2 31 34 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 68 134 (accept_3_2 61 68 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 68
  134 2 30 34 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  68 134 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 68 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 68 134 2 29 34 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 68 134 (Polychromatic418967fa.accept_9_3_5_8_1_99 57 68 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 68 134 2 28 34 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 68 134 (accept_3_2 55 68 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 68 134 2 27 34 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 68 134
  (Polychromatic418967fa.accept_7_4_5_1_1_418 53 68 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 68 134 2 26 34 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 68 134 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 68 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 68 134 2 25 34 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 68 134 (accept_3_2 49 68 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 68 134 2 24 34 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 68 134 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 68 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 68 134 2 23 34 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 68 134
  (Polychromatic418967fa.accept_7_3_5_1_1_72 45 68 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 68 134 2 22 34 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 68 134 (accept_3_2 43 68 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 68
  134 2 21 34 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  68 134 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 68 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 68 134 2 20 34 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 68 134 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 68 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 68 134 2 19 34 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 68 134 (accept_3_2 37 68 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 68 134 2 18 34 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 68 134
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 68 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 68 134 2 17 34 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 68 134 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 68 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 68 134 2 16 34 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 68 134 (accept_3_2 31 68 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 68 134 2 15 34 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 68 134 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 68 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 68 134 2 14 34 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 68 134
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 68 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 68 134 2 13 34 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 68 134 (accept_3_2 25 68 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 68
  134 2 12 34 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  68 134 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 68 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 68 134 2 11 34 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 68 134 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 68 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 68 134 2 10 34 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 68 134 (accept_3_2 19 68 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 68 134 2 9 34 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 68 134 (Polychromatic418967fa.accept_7_3_5_1_1_72 17
  68 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 68 134 2 8 34 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 68 134
  (Polychromatic418967fa.accept_9_6_5_8_1_598 15 68 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 68 134 2 7 34 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 68 134 (accept_3_2 13 68 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68
  134 2 6 34 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  68 134 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 68 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 68 134 2 5 34 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 68 134 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 68 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 68 134 2 4 34 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 68 134 (accept_3_2 7 68 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 134 2 3 34 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 68 134 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 68 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 68 134 2 2 34 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 68 134
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 68 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 68 134 2 1 34 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 68 134 (accept_3_2 1 68 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  134))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 134 (allA_of_3_0 67 67 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 134 (allA_succ_of_accept 65 66 134
  (Polychromatic418967fa.accept_7_2_3_1_1_10 65 66 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 66 134 2 32 33 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 66 134 (Polychromatic418967fa.accept_12_3_6_2_1_747 63 66 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 66 134 2 31 33 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 66 134 (accept_3_2 61 66 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 134 2 30 33 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 134 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 66 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 134 2 29 33 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 134
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 57 66 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 66 134 2 28 33 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 66 134 (accept_3_2 55 66 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 66
  134 2 27 33 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  66 134 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 66 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 66 134 2 26 33 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 66 134 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 66 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 66 134 2 25 33 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 66 134 (accept_3_2 49 66 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 134 2 24 33 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 134
  (Polychromatic418967fa.accept_7_5_3_1_1_424 47 66 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 66 134 2 23 33 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 66 134 (Polychromatic418967fa.accept_10_5_6_4_1_64 45 66 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 66 134 2 22 33 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 66 134 (accept_3_2 43 66 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 134 2 21 33 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 134 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 66 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 134 2 20 33 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 66 134
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 66 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 66 134 2 19 33 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 66 134 (accept_3_2 37 66 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66
  134 2 18 33 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  66 134 (Polychromatic418967fa.accept_10_5_6_4_1_64 35 66 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 66 134 2 17 33 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 66 134 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 66 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 66 134 2 16 33 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 66 134 (accept_3_2 31 66 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 134 2 15 33 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 134
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 66 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 66 134 2 14 33 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 66 134 (Polychromatic418967fa.accept_12_3_6_2_1_747 27 66 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 66 134 2 13 33 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 66 134 (accept_3_2 25 66 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 134 2 12 33 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 134 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 66 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 134 2 11 33 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 66 134
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 66 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 66 134 2 10 33 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 66 134 (accept_3_2 19 66 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66
  134 2 9 33 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  66 134 (Polychromatic418967fa.accept_16_1_2_6_1_2295 17 66 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 66 134 2 8 33 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 66 134 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 66 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 66 134 2 7 33 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 134 (accept_3_2 13 66 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 134 2 6 33 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 66 134 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 66 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66 134 2 5 33 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 66 134
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 66 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 66 134 2 4 33 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 66 134 (accept_3_2 7 66 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 134
  2 3 33 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66
  134 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 66 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 66 134 2 2 33 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 66 134 (Polychromatic418967fa.accept_12_3_6_2_1_747 3 66 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 66 134 2 1 33 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 134 (accept_3_2 1 66 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 66 134)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 134
  (allA_succ_of_accept 64 65 134 (accept_3_2 64 65 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  65 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 65 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 65 134 (Polychromatic418967fa.accept_7_6_2_1_1_214 62 65 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 134 (accept_3_2 61 65 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 65 134 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 65 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 134
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 65 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 65 134 (accept_3_2 58 65 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  65 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 65 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 65 134 (Polychromatic418967fa.accept_10_6_5_4_1_571 56 65 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 134 (accept_3_2 55 65 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 65 134 (Polychromatic418967fa.accept_15_9_5_14_1_973 54 65 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 134
  (Polychromatic418967fa.accept_15_8_5_14_1_986 53 65 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 65 134 (accept_3_2 52 65 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  65 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 65 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 65 134 (Polychromatic418967fa.accept_9_5_2_8_1_109 50 65 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 134 (accept_3_2 49 65 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 134 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 65 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 134
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 65 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 134 (accept_3_2 46 65 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 65 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 134 (Polychromatic418967fa.accept_12_8_5_2_1_746 44 65 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 134 (accept_3_2 43 65 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 134 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 65 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 134
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 65 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 134 (accept_3_2 40 65 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 65 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 134 (Polychromatic418967fa.accept_7_3_2_1_1_225 38 65 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 134 (accept_3_2 37 65 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 134 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 65 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 134
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 65 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 134 (accept_3_2 34 65 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 65 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 134 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 65 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 134 (accept_3_2 31 65 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 134 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 65 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 134
  (Polychromatic418967fa.accept_10_9_5_4_1_966 29 65 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 134 (accept_3_2 28 65 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 65 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 134 (Polychromatic418967fa.accept_10_6_5_4_1_571 26 65 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 134 (accept_3_2 25 65 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 134 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 65 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 134
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 65 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 134 (accept_3_2 22 65 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 65 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 134 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 65 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 134 (accept_3_2 19 65 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 134 (Polychromatic418967fa.accept_16_2_1_6_1_2342 18 65 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 134
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 65 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 134 (accept_3_2 16 65 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 65 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 134 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 65 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 134 (accept_3_2 13 65 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 134 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 65 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 134
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 65 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 134 (accept_3_2 10 65 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 65 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 134 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 65 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 134 (accept_3_2 7 65 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 134 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 65 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 134
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 65 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 134 (accept_3_2 4 65 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  134 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 65 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 134 (Polychromatic418967fa.accept_15_2_5_14_1_61 2 65 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 134 (accept_3_2 1 65 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 134))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 134
  (allA_of_3_0 64 64 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 63 134 (allA_succ_of_accept 62 63 134
  (Polychromatic418967fa.accept_13_10_11_4_1_2248 62 63 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 134 (accept_3_2 61 63 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 134 (Polychromatic418967fa.accept_11_5_8_2_1_588 60 63 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 63 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 134 (accept_3_2 58 63 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 63 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 134
  (Polychromatic418967fa.accept_15_11_3_14_1_971 56 63 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 134 (accept_3_2 55 63 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 134 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 63 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 63 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 134 (accept_3_2 52 63 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 134 (Polychromatic418967fa.accept_13_12_11_4_1_3111 51 63 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 134
  (Polychromatic418967fa.accept_22_6_19_2_1_6814 50 63 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 134 (accept_3_2 49 63 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 134 (Polychromatic418967fa.accept_14_6_7_8_1_624 48 63 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 63 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 134 (accept_3_2 46 63 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 63 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 134
  (Polychromatic418967fa.accept_20_4_3_14_1_6813 44 63 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 134 (accept_3_2 43 63 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  63 134 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 63 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 63 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 63 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 134 (accept_3_2 40 63 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 134 (Polychromatic418967fa.accept_10_9_3_4_1_985 39 63 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 134
  (Polychromatic418967fa.accept_11_5_8_2_1_588 38 63 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 134 (accept_3_2 37 63 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 134 (Polychromatic418967fa.accept_13_10_11_4_1_2248 36 63 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 63 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 134 (accept_3_2 34 63 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 63 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 134
  (Polychromatic418967fa.accept_13_6_11_4_1_938 32 63 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 134 (accept_3_2 31 63 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 134 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 63 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 63 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 134 (accept_3_2 28 63 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 134 (Polychromatic418967fa.accept_10_7_3_4_1_978 27 63 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 134
  (Polychromatic418967fa.accept_15_11_3_14_1_971 26 63 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 134 (accept_3_2 25 63 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 134 (Polychromatic418967fa.accept_18_6_9_8_1_6812 24 63 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 63 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 134 (accept_3_2 22 63 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 63 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 134
  (Polychromatic418967fa.accept_13_7_11_4_1_2247 20 63 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 134 (accept_3_2 19 63 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 134 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 63 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 63 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 134 (accept_3_2 16 63 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 134 (Polychromatic418967fa.accept_13_2_11_4_1_445 15 63 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 134
  (Polychromatic418967fa.accept_17_14_12_15_1_5558 14 63 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 63 134 (accept_3_2 13 63 134 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 63 134 (Polychromatic418967fa.accept_13_12_11_4_1_3111 12 63 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 63 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 134 (accept_3_2 10 63 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 63
  134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 134
  (Polychromatic418967fa.accept_13_8_11_4_1_1553 8 63 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 134 (accept_3_2 7 63 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  134 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 63 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 63 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 134 (accept_3_2 4 63 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 134 (Polychromatic418967fa.accept_17_3_12_15_1_1203 3 63 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 134 (Polychromatic418967fa.accept_13_2_11_4_1_445 2
  63 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 134 (accept_3_2 1 63 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  134))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 134 (allA_succ_of_accept 61 62 134
  (accept_3_2 61 62 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 62 134 2 30 31 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 62 134
  (Polychromatic418967fa.accept_13_7_10_4_1_919 59 62 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 62 134 2 29 31 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 62 134 (Polychromatic418967fa.accept_10_7_2_4_1_569 57 62 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 62 134 2 28 31 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 62 134 (accept_3_2 55 62 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 62 134 2 27 31 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 62 134 (Polychromatic418967fa.accept_11_9_7_2_1_1068 53 62 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 62 134 2 26 31 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 62 134
  (Polychromatic418967fa.accept_7_2_6_1_1_73 51 62 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 62 134 2 25 31 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 62 134 (accept_3_2 49 62 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 62
  134 2 24 31 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  62 134 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 62 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 62 134 2 23 31 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 62 134 (Polychromatic418967fa.accept_13_6_10_4_1_957 45 62 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 62 134 2 22 31 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 62 134 (accept_3_2 43 62 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 62 134 2 21 31 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 62 134
  (Polychromatic418967fa.accept_19_3_5_1_1_6811 41 62 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 62 134 2 20 31 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 62 134 (Polychromatic418967fa.accept_17_5_11_15_1_5445 39 62 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 62 134 2 19 31 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 62 134 (accept_3_2 37 62 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 62 134 2 18 31 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 62 134 (Polychromatic418967fa.accept_14_7_6_8_1_2856 35 62 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 62 134 2 17 31 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 62 134
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 62 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 62 134 2 16 31 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 62 134 (accept_3_2 31 62 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 62
  134 2 15 31 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  62 134 (Polychromatic418967fa.accept_22_7_18_2_1_6810 29 62 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 62 134 2 14 31 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 62 134 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 62 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 62 134 2 13 31 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 62 134 (accept_3_2 25 62 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 62 134 2 12 31 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 62 134
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 62 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 62 134 2 11 31 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 62 134 (Polychromatic418967fa.accept_13_8_10_4_1_2270 21 62 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 62 134 2 10 31 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 62 134 (accept_3_2 19 62 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 62 134 2 9 31 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 62 134 (Polychromatic418967fa.accept_10_7_2_4_1_569 17 62 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 134 2 8 31 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 134
  (Polychromatic418967fa.accept_19_15_5_1_1_5360 15 62 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 62 134 2 7 31 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 62 134 (accept_3_2 13 62 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62
  134 2 6 31 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  62 134 (Polychromatic418967fa.accept_13_11_10_4_1_1565 11 62 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 62 134 2 5 31 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 62 134 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 62 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 134 2 4 31 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 134 (accept_3_2 7 62 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 62 134 2 3 31 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 62 134 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 62 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 134 2 2 31 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 134
  (Polychromatic418967fa.accept_15_3_2_14_1_1713 3 62 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 62 134 2 1 31 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 62 134 (accept_3_2 1 62 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  134)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 134 (allA_of_3_0 61 61 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 134 (allA_succ_of_accept 59 60 134
  (Polychromatic418967fa.accept_7_3_4_1_1_71 59 60 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 60 134 2 29 30 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 60 134 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 60 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 60 134 2 28 30 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 60 134 (accept_3_2 55 60 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 134 2 27 30 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 134 (Polychromatic418967fa.accept_14_11_4_8_1_664 53 60 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 134 2 26 30 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 60 134
  (Polychromatic418967fa.accept_13_12_8_4_1_3099 51 60 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 60 134 2 25 30 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 60 134 (accept_3_2 49 60 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60
  134 2 24 30 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  60 134 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 60 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 60 134 2 23 30 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 60 134 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 60 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 60 134 2 22 30 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 134 (accept_3_2 43 60 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 134 2 21 30 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 134
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 60 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 60 134 2 20 30 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 60 134 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 60 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 60 134 2 19 30 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 134 (accept_3_2 37 60 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 134 2 18 30 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 134 (Polychromatic418967fa.accept_13_9_8_4_1_937 35 60 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 134 2 17 30 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 134
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 60 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 60 134 2 16 30 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 60 134 (accept_3_2 31 60 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60
  134 2 15 30 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  60 134 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 60 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 60 134 2 14 30 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 60 134 (Polychromatic418967fa.accept_18_9_6_8_1_2989 27 60 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 60 134 2 13 30 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 60 134 (accept_3_2 25 60 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 134 2 12 30 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 134
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 60 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 60 134 2 11 30 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 60 134 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 60 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 60 134 2 10 30 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 134 (accept_3_2 19 60 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 134 2 9 30 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 60 134 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 60 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60 134 2 8 30 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 60 134
  (Polychromatic418967fa.accept_21_15_18_8_1_6809 15 60 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 60 134 2 7 30 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 60 134 (accept_3_2 13 60 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60
  134 2 6 30 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  60 134 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 60 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 60 134 2 5 30 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 60 134 (Polychromatic418967fa.accept_13_9_8_4_1_937 9 60 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 60 134 2 4 30 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 134 (accept_3_2 7 60 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 134 2 3 30 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 60 134 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 60 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 134 2 2 30 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 60 134
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 60 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 60 134 2 1 30 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 60 134 (accept_3_2 1 60 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  134)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 134 (allA_succ_of_accept 58 59 134
  (accept_3_2 58 59 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 134
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 59 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 134 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 59 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 134 (accept_3_2 55 59 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 134 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 59 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 53
  59 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 59 134 (accept_3_2 52 59
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 59 134 (Polychromatic418967fa.accept_6_3_5_2_1_12
  51 59 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 59 134
  (Polychromatic418967fa.accept_11_6_4_2_1_599 50 59 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 59 134 (accept_3_2 49 59 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  59 134 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 59 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 59 134 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 59 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 59 134 (accept_3_2 46 59 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 59 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 59 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 59 134
  (Polychromatic418967fa.accept_7_2_3_1_1_10 44 59 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 59 134 (accept_3_2 43 59 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  59 134 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 59 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 59 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 59 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 59 134 (accept_3_2 40 59 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 59 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 59 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 59 134
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 59 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 59 134 (accept_3_2 37 59 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  59 134 (Polychromatic418967fa.accept_13_10_7_4_1_2262 36 59 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 59 134 (Polychromatic418967fa.accept_10_5_9_4_1_1420 35 59 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 59 134 (accept_3_2 34 59 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 59 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 59 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 59 134
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 59 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 59 134 (accept_3_2 31 59 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  59 134 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 59 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 59 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 59 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 59 134 (accept_3_2 28 59 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 59 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 59 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 59 134
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 59 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 59 134 (accept_3_2 25 59 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  59 134 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 59 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 59 134 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 59 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 59 134 (accept_3_2 22 59 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 59 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 59 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 59 134
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 59 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 59 134 (accept_3_2 19 59 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  59 134 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 59 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 59 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 59 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 59 134 (accept_3_2 16 59 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 59 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 59 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 59 134
  (Polychromatic418967fa.accept_18_14_5_8_1_1880 14 59 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 59 134 (accept_3_2 13 59 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  59 134 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 59 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 59 134 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 59 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 59 134 (accept_3_2 10 59 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 59 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 59 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 59 134
  (Polychromatic418967fa.accept_10_8_9_4_1_961 8 59 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 59 134 (accept_3_2 7 59 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 59
  134 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 59 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 59 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 59 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 134 (accept_3_2 4 59 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 59 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 59 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 134 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 59
  134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 134 (accept_3_2 1 59 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59 134)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 58 134 (allA_of_3_0 58 58 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 134
  (allA_succ_of_accept 56 57 134 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 57 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 134 (accept_3_2 55 57 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 57 134 (Polychromatic418967fa.accept_12_6_9_2_1_311 54 57 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 53
  57 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 134 (accept_3_2 52 57
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 134 (Polychromatic418967fa.accept_4_3_1_2_1_62
  51 57 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 134
  (Polychromatic418967fa.accept_9_5_3_8_1_316 50 57 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 134 (accept_3_2 49 57 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 134 (Polychromatic418967fa.accept_13_9_5_4_1_1591 48 57 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 57 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 134 (accept_3_2 46 57 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 134 (Polychromatic418967fa.accept_13_6_5_4_1_3924 45 57 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 134
  (Polychromatic418967fa.accept_14_2_1_8_1_650 44 57 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 134 (accept_3_2 43 57 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 134 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 57 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 57 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 134 (accept_3_2 40 57 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 57 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 134
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 57 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 134 (accept_3_2 37 57 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 134 (Polychromatic418967fa.accept_13_10_5_4_1_3107 36 57 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 57 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 134 (accept_3_2 34 57 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 134 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 57 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 134
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 57 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 134 (accept_3_2 31 57 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 134 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 57 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 57 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 134 (accept_3_2 28 57 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 57 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 134
  (Polychromatic418967fa.accept_15_11_12_14_1_2612 26 57 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 57 134 (accept_3_2 25 57 134 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 57 134 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 57 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 57 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 134 (accept_3_2 22 57 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 134 (Polychromatic418967fa.accept_10_1_7_4_1_968
  21 57 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 134
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 57 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 134 (accept_3_2 19 57 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 134 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 57 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 57 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 134 (accept_3_2 16 57 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 57 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 134
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 57 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 134 (accept_3_2 13 57 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 134 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 57 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 57 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 134 (accept_3_2 10 57 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 134 (Polychromatic418967fa.accept_13_9_5_4_1_1591 9 57 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 134
  (Polychromatic418967fa.accept_17_8_6_15_1_523 8 57 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 134 (accept_3_2 7 57 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  134 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 57 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 57 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 134 (accept_3_2 4 57 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 57 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 134 (Polychromatic418967fa.accept_9_2_3_8_1_318 2
  57 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 134 (accept_3_2 1 57 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 134)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 134 (allA_succ_of_accept 55 56 134 (accept_3_2 55 56 134 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 56 134 2 27 28 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 56 134 (Polychromatic418967fa.accept_12_5_8_2_1_309 53 56 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 56 134 2 26 28 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 56 134 (Polychromatic418967fa.accept_9_6_2_8_1_592 51
  56 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 56 134 2 25 28 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 56 134 (accept_3_2 49
  56 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 56 134 2 24 28 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 56 134
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 47 56 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 56 134 2 23 28 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 56 134 (Polychromatic418967fa.accept_10_5_6_4_1_64 45 56 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 56 134 2 22 28 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 56 134 (accept_3_2 43 56 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56 134 2 21 28 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 56 134 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 56 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 56 134 2 20 28 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 56 134
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 56 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 56 134 2 19 28 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 56 134 (accept_3_2 37 56 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 56
  134 2 18 28 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  56 134 (Polychromatic418967fa.accept_10_5_6_4_1_64 35 56 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 56 134 2 17 28 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 56 134 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 56 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 56 134 2 16 28 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 56 134 (accept_3_2 31 56 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 56 134 2 15 28 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 56 134
  (Polychromatic418967fa.accept_12_5_8_2_1_309 29 56 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 56 134 2 14 28 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 56 134 (Polychromatic418967fa.accept_15_12_11_14_1_3464 27 56 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 56 134 2 13 28 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 56 134 (accept_3_2 25 56 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 56 134 2 12 28 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 56 134 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 56 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 56 134 2 11 28 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 56 134
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 56 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 56 134 2 10 28 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 56 134 (accept_3_2 19 56 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56
  134 2 9 28 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  56 134 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 56 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 56 134 2 8 28 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 56 134 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 56 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 134 2 7 28 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 134 (accept_3_2 13 56 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56 134 2 6 28 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 56 134 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 56 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 56 134 2 5 28 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 56 134
  (Polychromatic418967fa.accept_23_9_10_19_1_6808 9 56 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 56 134 2 4 28 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 56 134 (accept_3_2 7 56 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 56 134
  2 3 28 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 56
  134 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 56 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 56 134 2 2 28 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 56 134 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 56 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 56 134 2 1 28 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 56 134 (accept_3_2 1 56 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 56 134)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 134 (allA_of_3_0 55
  55 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 134 (allA_succ_of_accept 53 54 134
  (Polychromatic418967fa.accept_7_4_5_1_1_418 53 54 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 54 134 2 26 27 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 54 134 (Polychromatic418967fa.accept_12_3_6_2_1_747 51 54 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 54 134 2 25 27 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 134 (accept_3_2 49 54 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 134 2 24 27 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 134 (Polychromatic418967fa.accept_21_5_12_8_1_6807 47 54 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 134 2 23 27 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 54 134
  (Polychromatic418967fa.accept_7_3_5_1_1_72 45 54 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 54 134 2 22 27 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 54 134 (accept_3_2 43 54 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54
  134 2 21 27 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  54 134 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 54 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 54 134 2 20 27 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 54 134 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 54 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 54 134 2 19 27 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 54 134 (accept_3_2 37 54 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 134 2 18 27 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 134
  (Polychromatic418967fa.accept_15_5_9_14_1_1724 35 54 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 54 134 2 17 27 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 54 134 (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 54 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 54 134 2 16 27 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 134 (accept_3_2 31 54 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 134 2 15 27 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 134 (Polychromatic418967fa.accept_17_12_3_15_1_5476 29 54
  134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 134 2 14 27 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54 134
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 54 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 54 134 2 13 27 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 54 134 (accept_3_2 25 54 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54
  134 2 12 27 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  54 134 (Polychromatic418967fa.accept_11_1_10_2_1_58 23 54 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 54 134 2 11 27 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 54 134 (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 54 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 54 134 2 10 27 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 134 (accept_3_2 19 54 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 134 2 9 27 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 134 (Polychromatic418967fa.accept_7_3_5_1_1_72 17
  54 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 134 2 8 27 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 54 134
  (Polychromatic418967fa.accept_12_3_6_2_1_747 15 54 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 54 134 2 7 27 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 54 134 (accept_3_2 13 54 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54
  134 2 6 27 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  54 134 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 54 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 54 134 2 5 27 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 54 134 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 54 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 54 134 2 4 27 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 134 (accept_3_2 7 54 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 134 2 3 27 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 54 134 (Polychromatic418967fa.accept_13_5_2_4_1_3955 5 54 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 134 2 2 27 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 54 134
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 54 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 54 134 2 1 27 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 54 134 (accept_3_2 1 54 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  134)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 134 (allA_succ_of_accept 52 53 134 (accept_3_2
  52 53 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 134
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 53 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 134 (Polychromatic418967fa.accept_15_5_8_14_1_432 50 53 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 134 (accept_3_2 49 53 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 134 (Polychromatic418967fa.accept_11_4_9_2_1_259 48 53 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 47
  53 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 134 (accept_3_2 46 53
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 134 (Polychromatic418967fa.accept_6_3_5_2_1_12
  45 53 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 53 134
  (Polychromatic418967fa.accept_12_8_5_2_1_746 44 53 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 53 134 (accept_3_2 43 53 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  53 134 (Polychromatic418967fa.accept_13_3_1_4_1_945 42 53 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 53 134 (Polychromatic418967fa.accept_17_7_2_15_1_1255 41 53 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 134 (accept_3_2 40 53 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 53 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 53 134
  (Polychromatic418967fa.accept_7_3_4_1_1_71 38 53 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 53 134 (accept_3_2 37 53 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  53 134 (Polychromatic418967fa.accept_13_10_1_4_1_3103 36 53 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 53 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 53 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 53 134 (accept_3_2 34 53 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 53 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 53 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 53 134
  (Polychromatic418967fa.accept_12_8_5_2_1_746 32 53 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 53 134 (accept_3_2 31 53 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  53 134 (Polychromatic418967fa.accept_17_13_2_15_1_2151 30 53 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 53 134 (Polychromatic418967fa.accept_10_9_3_4_1_985 29 53 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 134 (accept_3_2 28 53 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 53 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 53 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 53 134
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 53 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 53 134 (accept_3_2 25 53 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  53 134 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 53 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 53 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 53 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 53 134 (accept_3_2 22 53 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 53 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 53 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 53 134
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 53 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 53 134 (accept_3_2 19 53 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  53 134 (Polychromatic418967fa.accept_11_7_9_2_1_260 18 53 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 53 134 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 53 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 134 (accept_3_2 16 53 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 53 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 53 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 134
  (Polychromatic418967fa.accept_19_14_15_1_1_6806 14 53 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 53 134 (accept_3_2 13 53 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  53 134 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 53 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 53 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 53 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 134 (accept_3_2 10 53 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 53 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 53 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 134
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 53 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 53 134 (accept_3_2 7 53 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53
  134 (Polychromatic418967fa.accept_15_6_8_14_1_4575 6 53 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 53 134 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 53 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 53 134 (accept_3_2 4 53 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 53 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 53 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 53 134
  (Polychromatic418967fa.accept_18_2_17_8_1_1893 2 53 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 53 134 (accept_3_2 1 53 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 53
  134))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 134 (allA_of_3_0 52 52 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 51 134 (allA_succ_of_accept 50 51 134 (Polychromatic418967fa.accept_9_5_6_8_1_101 50
  51 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 134 (accept_3_2 49 51
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 51 134
  (Polychromatic418967fa.accept_7_6_2_1_1_214 48 51 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 51 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 51 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 134 (accept_3_2 46 51 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 51 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 51 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 134 (Polychromatic418967fa.accept_13_5_12_4_1_449
  44 51 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 134 (accept_3_2 43
  51 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 51 134
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 42 51 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 51 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 51 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 134 (accept_3_2 40 51 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 51 134 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 51 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 134 (Polychromatic418967fa.accept_7_3_2_1_1_225 38
  51 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 134 (accept_3_2 37 51
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 51 134
  (Polychromatic418967fa.accept_16_4_3_6_1_6805 36 51 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 51 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 51 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 134 (accept_3_2 34 51 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 51 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 51 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 134 (Polychromatic418967fa.accept_9_5_6_8_1_101 32
  51 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 134 (accept_3_2 31 51
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 51 134
  (Polychromatic418967fa.accept_9_3_6_8_1_308 30 51 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 51 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 51 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 134 (accept_3_2 28 51 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 51 134 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 51 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 134 (Polychromatic418967fa.accept_19_7_13_1_1_6804
  26 51 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 134 (accept_3_2 25
  51 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 51 134
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 51 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 51 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 51 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 134 (accept_3_2 22 51 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 51 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 51 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 134 (Polychromatic418967fa.accept_7_6_2_1_1_214 20
  51 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 134 (accept_3_2 19 51
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 51 134
  (Polychromatic418967fa.accept_12_6_3_2_1_743 18 51 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 51 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 51 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 134 (accept_3_2 16 51 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 51 134 (Polychromatic418967fa.accept_10_5_1_4_1_1444 15 51 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 134 (Polychromatic418967fa.accept_9_5_6_8_1_101 14
  51 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 134 (accept_3_2 13 51
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 134
  (Polychromatic418967fa.accept_9_3_6_8_1_308 12 51 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 51 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 51 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 134 (accept_3_2 10 51 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 51 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 51 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 134 (Polychromatic418967fa.accept_13_8_12_4_1_4858
  8 51 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 134 (accept_3_2 7 51
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 134 (Polychromatic418967fa.accept_7_6_2_1_1_214
  6 51 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 134
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 51 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 51 134 (accept_3_2 4 51 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51
  134 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 51 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 51 134 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 51 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 134 (accept_3_2 1 51 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 51 134))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 134 (allA_succ_of_accept
  49 50 134 (accept_3_2 49 50 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 50 134 2 24 25 67
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 50 134
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 50 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 50 134 2 23 25 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 50 134 (Polychromatic418967fa.accept_13_6_11_4_1_938 45 50 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 50 134 2 22 25 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 50 134 (accept_3_2 43 50 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 50 134 2 21 25 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 50 134 (Polychromatic418967fa.accept_13_2_11_4_1_445 41 50 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 50 134 2 20 25 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 50 134
  (Polychromatic418967fa.accept_9_3_5_8_1_99 39 50 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 50 134 2 19 25 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 50 134 (accept_3_2 37 50 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 50
  134 2 18 25 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  50 134 (Polychromatic418967fa.accept_16_3_2_6_1_4461 35 50 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 50 134 2 17 25 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 50 134 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 50 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 50 134 2 16 25 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 50 134 (accept_3_2 31 50 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50 134 2 15 25 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 50 134
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 50 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 50 134 2 14 25 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 50 134 (Polychromatic418967fa.accept_16_11_2_6_1_1435 27 50 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 50 134 2 13 25 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 50 134 (accept_3_2 25 50 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 50 134 2 12 25 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 50 134 (Polychromatic418967fa.accept_13_10_11_4_1_2248 23 50
  134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 50 134 2 11 25 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 50 134
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 50 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 50 134 2 10 25 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 50 134 (accept_3_2 19 50 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 50
  134 2 9 25 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  50 134 (Polychromatic418967fa.accept_15_2_5_14_1_61 17 50 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 50 134 2 8 25 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 50 134 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 50 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 50 134 2 7 25 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 50 134 (accept_3_2 13 50 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50 134 2 6 25 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 50 134 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 50 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 50 134 2 5 25 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 50 134
  (Polychromatic418967fa.accept_15_9_5_14_1_973 9 50 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 50 134 2 4 25 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 50 134 (accept_3_2 7 50 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 50 134
  2 3 25 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 50
  134 (Polychromatic418967fa.accept_18_5_14_8_1_2966 5 50 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 50 134 2 2 25 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 50 134 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 50 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 50 134 2 1 25 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 50 134 (accept_3_2 1 50 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 50 134)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 134 (allA_of_3_0
  49 49 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 134 (allA_succ_of_accept 47 48 134
  (Polychromatic418967fa.accept_7_5_6_1_1_407 47 48 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 48 134 2 23 24 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 48 134 (Polychromatic418967fa.accept_13_6_9_4_1_2288 45 48 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 48 134 2 22 24 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 48 134 (accept_3_2 43 48 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 134 2 21 24 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 134 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 48 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 134 2 20 24 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 48 134
  (Polychromatic418967fa.accept_10_9_8_4_1_970 39 48 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 48 134 2 19 24 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 48 134 (accept_3_2 37 48 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48
  134 2 18 24 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  48 134 (Polychromatic418967fa.accept_14_7_6_8_1_2856 35 48 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 48 134 2 17 24 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 48 134 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 48 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 48 134 2 16 24 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 48 134 (accept_3_2 31 48 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 134 2 15 24 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 134
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 48 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 48 134 2 14 24 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 48 134 (Polychromatic418967fa.accept_22_5_4_2_1_6803 27 48 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 48 134 2 13 24 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 134 (accept_3_2 25 48 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 134 2 12 24 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 134 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 48 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 134 2 11 24 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 48 134
  (Polychromatic418967fa.accept_13_8_9_4_1_1552 21 48 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 48 134 2 10 24 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 48 134 (accept_3_2 19 48 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48
  134 2 9 24 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  48 134 (Polychromatic418967fa.accept_11_6_4_2_1_599 17 48 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 48 134 2 8 24 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 48 134 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 48 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 48 134 2 7 24 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 134 (accept_3_2 13 48 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 134 2 6 24 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 48 134 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 48 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 134 2 5 24 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 48 134
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 48 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 48 134 2 4 24 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 48 134 (accept_3_2 7 48 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 134
  2 3 24 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48
  134 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 48 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 48 134 2 2 24 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 48 134 (Polychromatic418967fa.accept_17_3_14_15_1_5502 3 48 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 134 2 1 24 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 134 (accept_3_2 1 48 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 48 134)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 134 (allA_succ_of_accept 46
  47 134 (accept_3_2 46 47 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 134
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 47 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 134 (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 47 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 134 (accept_3_2 43 47 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 134 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 47 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 41
  47 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 134 (accept_3_2 40 47
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 134 (Polychromatic418967fa.accept_6_3_5_2_1_12
  39 47 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 47 134
  (Polychromatic418967fa.accept_7_3_5_1_1_72 38 47 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 47 134 (accept_3_2 37 47 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  47 134 (Polychromatic418967fa.accept_13_10_8_4_1_3098 36 47 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 47 134 (Polychromatic418967fa.accept_13_9_8_4_1_937 35 47 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 134 (accept_3_2 34 47 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 47 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 47 134
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 47 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 47 134 (accept_3_2 31 47 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  47 134 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 47 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 47 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 47 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 134 (accept_3_2 28 47 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 47 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 47 134
  (Polychromatic418967fa.accept_31_26_16_10_1_6802 26 47 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 47 134 (accept_3_2 25 47 134 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 47 134 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 47 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 134 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 47 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 134 (accept_3_2 22 47 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 21
  47 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 47 134
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 47 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 47 134 (accept_3_2 19 47 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  47 134 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 47 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 47 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 47 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 134 (accept_3_2 16 47 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 47 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 134
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 47 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 47 134 (accept_3_2 13 47 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  47 134 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 47 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 47 134 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 47 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 134 (accept_3_2 10 47 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 47 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 47 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 134
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 47 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 47 134 (accept_3_2 7 47 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47
  134 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 47 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 47 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 47 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 134 (accept_3_2 4 47 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 47 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 47 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 134 (Polychromatic418967fa.accept_10_2_7_4_1_967 2
  47 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 134 (accept_3_2 1 47 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47 134))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46
  134 (allA_of_3_0 46 46 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 134 (allA_succ_of_accept 44 45 134
  (Polychromatic418967fa.accept_7_2_3_1_1_10 44 45 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 134 (accept_3_2 43 45 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 134 (Polychromatic418967fa.accept_12_6_9_2_1_311 42 45 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 45 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 134 (accept_3_2 40 45 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 45 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 134
  (Polychromatic418967fa.accept_17_4_11_15_1_3170 38 45 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 134 (accept_3_2 37 45 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  45 134 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 45 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 45 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 45 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 134 (accept_3_2 34 45 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 134 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 45 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 134
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 45 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 134 (accept_3_2 31 45 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  45 134 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 45 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 45 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 45 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 134 (accept_3_2 28 45 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 45 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 134
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 45 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 134 (accept_3_2 25 45 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  45 134 (Polychromatic418967fa.accept_13_11_6_4_1_3121 24 45 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 45 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 134 (accept_3_2 22 45 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 134 (Polychromatic418967fa.accept_10_1_5_4_1_276 21 45 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 134
  (Polychromatic418967fa.accept_13_7_6_4_1_933 20 45 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 134 (accept_3_2 19 45 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  45 134 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 45 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 45 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 134 (accept_3_2 16 45 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 45 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 134
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 14 45 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 134 (accept_3_2 13 45 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  45 134 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 45 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 45 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 134 (accept_3_2 10 45 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 134 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 45 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 134
  (Polychromatic418967fa.accept_19_8_7_1_1_6801 8 45 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 134 (accept_3_2 7 45 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  134 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 45 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 45 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 134 (accept_3_2 4 45 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 45 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 134 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 45
  134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 134 (accept_3_2 1 45 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 134))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  134 (allA_succ_of_accept 43 44 134 (accept_3_2 43 44 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42
  44 134 2 21 22 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 44 134 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 44 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 44 134 2 20 22 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 44 134 (Polychromatic418967fa.accept_17_5_10_15_1_5574 39 44 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 134 2 19 22 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 134 (accept_3_2 37 44 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 134 2 18 22 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44 134
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 44 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 44 134 2 17 22 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 44 134 (Polychromatic418967fa.accept_19_14_6_1_1_4022 33 44 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 44 134 2 16 22 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 44 134 (accept_3_2 31 44 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44 134 2 15 22 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 44 134 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 44 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 44 134 2 14 22 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 44 134
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 44 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 44 134 2 13 22 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 44 134 (accept_3_2 25 44 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 44
  134 2 12 22 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  44 134 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 44 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 44 134 2 11 22 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 44 134 (Polychromatic418967fa.accept_17_4_10_15_1_5444 21 44 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 44 134 2 10 22 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 44 134 (accept_3_2 19 44 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44 134 2 9 22 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 44 134 (Polychromatic418967fa.accept_7_3_2_1_1_225 17
  44 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 44 134 2 8 22 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 44 134
  (Polychromatic418967fa.accept_13_2_5_4_1_3926 15 44 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 44 134 2 7 22 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 44 134 (accept_3_2 13 44 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44
  134 2 6 22 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  44 134 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 44 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 44 134 2 5 22 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 44 134 (Polychromatic418967fa.accept_13_9_5_4_1_1591 9 44 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 44 134 2 4 22 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 44 134 (accept_3_2 7 44 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 134 2 3 22 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 44 134 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 44 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 44 134 2 2 22 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 44 134
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 44 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 44 134 2 1 22 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 44 134 (accept_3_2 1 44 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44
  134)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 134 (allA_of_3_0 43 43 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 42 134 (allA_succ_of_accept 41 42 134 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 42 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42 134 2 20 21 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 42 134
  (Polychromatic418967fa.accept_9_3_6_8_1_308 39 42 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 42 134 2 19 21 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 42 134 (accept_3_2 37 42 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42
  134 2 18 21 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  42 134 (Polychromatic418967fa.accept_19_16_4_1_1_5376 35 42 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 42 134 2 17 21 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 42 134 (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 42 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 42 134 2 16 21 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 42 134 (accept_3_2 31 42 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 134 2 15 21 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 134
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 42 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 42 134 2 14 21 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 42 134 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 42 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 42 134 2 13 21 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 134 (accept_3_2 25 42 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 134 2 12 21 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 134 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 42 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 134 2 11 21 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 42 134
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 42 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 42 134 2 10 21 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 42 134 (accept_3_2 19 42 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42
  134 2 9 21 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  42 134 (Polychromatic418967fa.accept_10_7_2_4_1_569 17 42 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 42 134 2 8 21 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 42 134 (Polychromatic418967fa.accept_11_4_9_2_1_259 15 42 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 134 2 7 21 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 134 (accept_3_2 13 42 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 134 2 6 21 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 42 134 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 42 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 134 2 5 21 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 42 134
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 42 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 42 134 2 4 21 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 42 134 (accept_3_2 7 42 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 134
  2 3 21 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42
  134 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 42 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 42 134 2 2 21 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 42 134 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 42 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 134 2 1 21 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 134 (accept_3_2 1 42 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 42 134)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 134 (allA_succ_of_accept 40 41
  134 (accept_3_2 40 41 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 134
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 41 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 134 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 41 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 134 (accept_3_2 37 41 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 134 (Polychromatic418967fa.accept_17_2_7_15_1_5525 36 41 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 134
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 41 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 134 (accept_3_2 34 41 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 41 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 134 (Polychromatic418967fa.accept_12_8_5_2_1_746 32 41 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 134 (accept_3_2 31 41 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 134 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 41 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 134
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 41 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 134 (accept_3_2 28 41 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 41 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 134 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 41 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 134 (accept_3_2 25 41 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 134 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 41 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 134
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 41 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 134 (accept_3_2 22 41 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 41 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 134 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 41 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 134 (accept_3_2 19 41 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 134 (Polychromatic418967fa.accept_13_5_2_4_1_3955 18 41 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 134
  (Polychromatic418967fa.accept_10_7_1_4_1_1447 17 41 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 134 (accept_3_2 16 41 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 41 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 134 (Polychromatic418967fa.accept_18_14_5_8_1_1880 14 41 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 134 (accept_3_2 13 41 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 134 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 41 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 134
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 41 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 134 (accept_3_2 10 41 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 41 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 134 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 41 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 134 (accept_3_2 7 41 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 134 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 41 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 134
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 41 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 134 (accept_3_2 4 41 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  134 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 41 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 134 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 41 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 134 (accept_3_2 1 41 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 134))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 134 (allA_of_3_0 40 40 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 134 (allA_succ_of_accept 38 39 134
  (Polychromatic418967fa.accept_7_3_4_1_1_71 38 39 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 134 (accept_3_2 37 39 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 134 (Polychromatic418967fa.accept_15_6_9_14_1_3457 36 39 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 39 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 134 (accept_3_2 34 39 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 39 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 134
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 39 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 134 (accept_3_2 31 39 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 134 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 39 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 39 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 134 (accept_3_2 28 39 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 134 (Polychromatic418967fa.accept_15_12_9_14_1_2635 27 39 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 134
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 39 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 134 (accept_3_2 25 39 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 134 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 39 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 39 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 134 (accept_3_2 22 39 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 39 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 134
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 39 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 134 (accept_3_2 19 39 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 134 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 39 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 39 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 134 (accept_3_2 16 39 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 134 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 39 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 134
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 39 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 134 (accept_3_2 13 39 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 134 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 39 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 39 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 134 (accept_3_2 10 39 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 39 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 134
  (Polychromatic418967fa.accept_10_8_9_4_1_961 8 39 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 134 (accept_3_2 7 39 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  134 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 39 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 39 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 134 (accept_3_2 4 39 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 134 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 39 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 134 (Polychromatic418967fa.accept_9_2_3_8_1_318 2
  39 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 134 (accept_3_2 1 39 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 134))))))))))))))))))))))))))))))))))))))) (allB_succ 38 134
  (allA_succ_of_accept 37 38 134 (accept_3_2 37 38 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38
  134 2 18 19 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  38 134 (Polychromatic418967fa.accept_15_5_8_14_1_432 35 38 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 38 134 2 17 19 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 38 134 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 38 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 134 2 16 19 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 134 (accept_3_2 31 38 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 134 2 15 19 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 134
  (Polychromatic418967fa.accept_10_9_8_4_1_970 29 38 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 134 2 14 19 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 38 134 (Polychromatic418967fa.accept_17_10_4_15_1_2165 27 38 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 134 2 13 19 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 134 (accept_3_2 25 38 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 134 2 12 19 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 134 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 38 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 38 134 2 11 19 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 38 134
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 38 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 38 134 2 10 19 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 38 134 (accept_3_2 19 38 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 38
  134 2 9 19 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  38 134 (Polychromatic418967fa.accept_18_17_2_8_1_6800 17 38 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 38 134 2 8 19 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 38 134 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 38 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 134 2 7 19 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 134 (accept_3_2 13 38 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 134 2 6 19 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 38 134 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 38 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 38 134 2 5 19 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 38 134
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 38 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 38 134 2 4 19 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 38 134 (accept_3_2 7 38 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 38 134
  2 3 19 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 38
  134 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 38 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 38 134 2 2 19 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 38 134 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 38 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 134 2 1 19 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 134 (accept_3_2 1 38 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 38 134)))))))))))))))))))))))))))))))))))))) (allB_succ 37 134 (allA_of_3_0 37 37 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 36 134 (allA_succ_of_accept 35 36 134
  (Polychromatic418967fa.accept_10_5_6_4_1_64 35 36 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 36 134 2 17 18 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 36 134 (Polychromatic418967fa.accept_13_7_10_4_1_919 33 36 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 36 134 2 16 18 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 134 (accept_3_2 31 36 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 134 2 15 18 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 134 (Polychromatic418967fa.accept_16_13_4_6_1_2322 29 36 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 134 2 14 18 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 134
  (Polychromatic418967fa.accept_13_1_10_4_1_954 27 36 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 36 134 2 13 18 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 36 134 (accept_3_2 25 36 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36
  134 2 12 18 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  36 134 (Polychromatic418967fa.accept_11_1_3_2_1_1090 23 36 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 36 134 2 11 18 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 36 134 (Polychromatic418967fa.accept_13_8_10_4_1_2270 21 36 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 36 134 2 10 18 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 134 (accept_3_2 19 36 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 134 2 9 18 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 134 (Polychromatic418967fa.accept_21_17_15_8_1_6799
  17 36 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 134 2 8 18 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 36 134
  (Polychromatic418967fa.accept_10_5_6_4_1_64 15 36 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 36 134 2 7 18 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 36 134 (accept_3_2 13 36 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36
  134 2 6 18 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  36 134 (Polychromatic418967fa.accept_13_11_10_4_1_1565 11 36 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 36 134 2 5 18 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 36 134 (Polychromatic418967fa.accept_15_9_6_14_1_2627 9 36 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 36 134 2 4 18 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 134 (accept_3_2 7 36 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 134 2 3 18 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 36 134 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 36 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 134 2 2 18 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 36 134
  (Polychromatic418967fa.accept_16_3_4_6_1_6798 3 36 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 36 134 2 1 18 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 36 134 (accept_3_2 1 36 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36
  134)))))))))))))))))))))))))))))))))))) (allB_succ 35 134 (allA_succ_of_accept 34 35 134 (accept_3_2 34 35 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 33
  35 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 35 134
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 35 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 35 134 (accept_3_2 31 35 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  35 134 (Polychromatic418967fa.accept_20_10_15_14_1_6797 30 35 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 35 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 35 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 134 (accept_3_2 28 35 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 35 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 134
  (Polychromatic418967fa.accept_10_6_5_4_1_571 26 35 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 35 134 (accept_3_2 25 35 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  35 134 (Polychromatic418967fa.accept_15_9_5_14_1_973 24 35 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 35 134 (Polychromatic418967fa.accept_15_8_5_14_1_986 23 35 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 134 (accept_3_2 22 35 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 35 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 35 134
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 35 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 35 134 (accept_3_2 19 35 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  35 134 (Polychromatic418967fa.accept_13_5_9_4_1_441 18 35 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 35 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 35 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 134 (accept_3_2 16 35 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 35 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 35 134
  (Polychromatic418967fa.accept_27_14_8_26_1_6796 14 35 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 35 134 (accept_3_2 13 35 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  35 134 (Polychromatic418967fa.accept_17_12_1_15_1_5472 12 35 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 35 134 (Polychromatic418967fa.accept_10_1_5_4_1_276 11 35 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 134 (accept_3_2 10 35 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 35 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 134
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 35 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 35 134 (accept_3_2 7 35 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35
  134 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 35 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 35 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 35 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 134 (accept_3_2 4 35 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 35 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 35 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 134 (Polychromatic418967fa.accept_15_2_5_14_1_61 2
  35 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 134 (accept_3_2 1 35 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35 134))))))))))))))))))))))))))))))))))) (allB_succ 34 134
  (allA_of_3_0 34 34 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 33 134 (allA_succ_of_accept 32 33 134
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 33 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 134 (accept_3_2 31 33 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  33 134 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 33 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 33 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 33 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 134 (accept_3_2 28 33 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 33 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 134
  (Polychromatic418967fa.accept_15_11_3_14_1_971 26 33 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 134 (accept_3_2 25 33 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  33 134 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 33 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 33 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 33 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 134 (accept_3_2 22 33 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 134 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 33 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 134
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 33 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 134 (accept_3_2 19 33 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  33 134 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 33 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 33 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 33 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 134 (accept_3_2 16 33 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 33 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 134
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 33 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 134 (accept_3_2 13 33 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  33 134 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 33 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 33 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 33 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 134 (accept_3_2 10 33 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 134 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 33 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 134
  (Polychromatic418967fa.accept_20_8_13_14_1_5321 8 33 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 134 (accept_3_2 7 33 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33
  134 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 33 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 33 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 134 (accept_3_2 4 33 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 33 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 33 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 134 (Polychromatic418967fa.accept_9_2_6_8_1_321 2
  33 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 134 (accept_3_2 1 33 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 134))))))))))))))))))))))))))))))))) (allB_succ 32 134
  (allA_succ_of_accept 31 32 134 (accept_3_2 31 32 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32
  134 2 15 16 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  32 134 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 32 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 32 134 2 14 16 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 32 134 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 32 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 134 2 13 16 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 134 (accept_3_2 25 32 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 134 2 12 16 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 32 134
  (Polychromatic418967fa.accept_11_1_10_2_1_58 23 32 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 32 134 2 11 16 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 32 134 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 32 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 32 134 2 10 16 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 32 134 (accept_3_2 19 32 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32 134 2 9 16 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 32 134 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 32 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 32 134 2 8 16 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 32 134
  (Polychromatic418967fa.accept_9_6_5_8_1_598 15 32 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 32 134 2 7 16 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 32 134 (accept_3_2 13 32 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32
  134 2 6 16 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  32 134 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 32 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 32 134 2 5 16 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 32 134 (Polychromatic418967fa.accept_13_9_6_4_1_2243 9 32 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 32 134 2 4 16 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 32 134 (accept_3_2 7 32 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 134 2 3 16 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 32 134 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 32 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 32 134 2 2 16 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 32 134
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 32 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 32 134 2 1 16 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 32 134 (accept_3_2 1 32 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32
  134)))))))))))))))))))))))))))))))) (allB_succ 31 134 (allA_of_3_0 31 31 134 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 30 134 (allA_succ_of_accept 29 30 134 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 30 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30 134 2 14 15 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 30 134
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 30 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 30 134 2 13 15 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 30 134 (accept_3_2 25 30 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30
  134 2 12 15 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  30 134 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 30 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 30 134 2 11 15 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 30 134 (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 30 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 30 134 2 10 15 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 134 (accept_3_2 19 30 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 134 2 9 15 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 134 (Polychromatic418967fa.accept_7_3_2_1_1_225 17
  30 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 134 2 8 15 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 30 134
  (Polychromatic418967fa.accept_9_6_3_8_1_595 15 30 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 30 134 2 7 15 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 30 134 (accept_3_2 13 30 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30
  134 2 6 15 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  30 134 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 30 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 30 134 2 5 15 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 30 134 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 30 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 30 134 2 4 15 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 134 (accept_3_2 7 30 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 134 2 3 15 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 30 134 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 30 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 30 134 2 2 15 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 30 134
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 30 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 30 134 2 1 15 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 30 134 (accept_3_2 1 30 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30
  134)))))))))))))))))))))))))))))) (allB_succ 29 134 (allA_succ_of_accept 28 29 134 (accept_3_2 28 29 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 29 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 134
  (Polychromatic418967fa.accept_19_7_10_1_1_5382 26 29 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 29 134 (accept_3_2 25 29 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  29 134 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 29 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 29 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 29 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 134 (accept_3_2 22 29 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 29 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 134
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 20 29 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 29 134 (accept_3_2 19 29 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  29 134 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 29 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 29 134 (Polychromatic418967fa.accept_19_17_10_1_1_6795 17 29 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 134 (accept_3_2 16 29 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 29 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 134
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 29 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 29 134 (accept_3_2 13 29 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  29 134 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 29 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 29 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 29 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 134 (accept_3_2 10 29 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 29 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 134
  (Polychromatic418967fa.accept_10_8_9_4_1_961 8 29 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 29 134 (accept_3_2 7 29 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29
  134 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 29 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 29 134 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 29 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 134 (accept_3_2 4 29 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 29 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 29 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 134 (Polychromatic418967fa.accept_14_2_1_8_1_650 2
  29 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 134 (accept_3_2 1 29 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29 134))))))))))))))))))))))))))))) (allB_succ 28 134 (allA_of_3_0
  28 28 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 27 134 (allA_succ_of_accept 26 27 134
  (Polychromatic418967fa.accept_7_5_6_1_1_407 26 27 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 134 (accept_3_2 25 27 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  27 134 (Polychromatic418967fa.accept_15_9_12_14_1_963 24 27 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 27 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 27 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 134 (accept_3_2 22 27 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 27 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 134
  (Polychromatic418967fa.accept_16_4_11_6_1_5591 20 27 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 134 (accept_3_2 19 27 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  27 134 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 27 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 27 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 27 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 134 (accept_3_2 16 27 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 134 (Polychromatic418967fa.accept_19_15_8_1_1_6794 15 27 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 134
  (Polychromatic418967fa.accept_21_14_6_8_1_1285 14 27 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 134 (accept_3_2 13 27 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  27 134 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 27 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 27 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 27 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 134 (accept_3_2 10 27 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 27 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 134
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 8 27 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 134 (accept_3_2 7 27 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27
  134 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 27 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 27 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 134 (accept_3_2 4 27 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 27 134 (Polychromatic418967fa.accept_10_3_7_4_1_584 3 27 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 134 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 27
  134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 134 (accept_3_2 1 27 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 134))))))))))))))))))))))))))) (allB_succ 26 134
  (allA_succ_of_accept 25 26 134 (accept_3_2 25 26 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26
  134 2 12 13 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  26 134 (Polychromatic418967fa.accept_17_6_9_15_1_3185 23 26 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 26 134 2 11 13 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 26 134 (Polychromatic418967fa.accept_19_2_7_1_1_2808 21 26 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 134 2 10 13 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 134 (accept_3_2 19 26 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 134 2 9 13 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 26 134 (Polychromatic418967fa.accept_7_3_5_1_1_72 17
  26 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 26 134 2 8 13 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 26 134
  (Polychromatic418967fa.accept_10_5_6_4_1_64 15 26 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 26 134 2 7 13 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 26 134 (accept_3_2 13 26 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26
  134 2 6 13 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  26 134 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 26 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 26 134 2 5 13 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 26 134 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 26 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 26 134 2 4 13 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 26 134 (accept_3_2 7 26 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 134 2 3 13 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 26 134 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 26 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 26 134 2 2 13 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 26 134
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 26 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 26 134 2 1 13 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 26 134 (accept_3_2 1 26 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  134)))))))))))))))))))))))))) (allB_succ 25 134 (allA_of_3_0 25 25 134 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 24 134 (allA_succ_of_accept 23 24 134 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 24 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 134 2 11 12 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 24 134
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 24 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 24 134 2 10 12 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 24 134 (accept_3_2 19 24 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24
  134 2 9 12 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  24 134 (Polychromatic418967fa.accept_21_17_3_8_1_6793 17 24 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 24 134 2 8 12 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 24 134 (Polychromatic418967fa.accept_13_2_11_4_1_445 15 24 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 134 2 7 12 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 134 (accept_3_2 13 24 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 134 2 6 12 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 24 134 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 24 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 134 2 5 12 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 24 134
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 24 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 24 134 2 4 12 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 24 134 (accept_3_2 7 24 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 134
  2 3 12 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24
  134 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 24 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 24 134 2 2 12 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 24 134 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 24 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 134 2 1 12 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 134 (accept_3_2 1 24 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 24 134)))))))))))))))))))))))) (allB_succ 23 134 (allA_succ_of_accept 22 23 134 (accept_3_2 22
  23 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 134
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 23 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 134 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 23 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 134 (accept_3_2 19 23 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 134 (Polychromatic418967fa.accept_13_5_10_4_1_1564 18 23 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 134
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 23 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 23 134 (accept_3_2 16 23 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  23 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 23 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 23 134 (Polychromatic418967fa.accept_11_3_1_2_1_1063 14 23 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 134 (accept_3_2 13 23 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 23 134 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 23 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 134
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 23 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 134 (accept_3_2 10 23 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  23 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 23 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 23 134 (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 23 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 134 (accept_3_2 7 23 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 23 134 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 23 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 23
  134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 134 (accept_3_2 4 23 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 23
  134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 134
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 23 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 23 134 (accept_3_2 1 23 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23
  134))))))))))))))))))))))) (allB_succ 22 134 (allA_of_3_0 22 22 134 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 21 134 (allA_succ_of_accept 20 21 134 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 21 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 134 (accept_3_2 19 21 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 134 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 21 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 134
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 21 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 134 (accept_3_2 16 21 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  21 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 21 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 21 134 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 21 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 134 (accept_3_2 13 21 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 134 (Polychromatic418967fa.accept_11_1_10_2_1_58 12 21 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 134
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 21 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 134 (accept_3_2 10 21 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  21 134 (Polychromatic418967fa.accept_13_9_8_4_1_937 9 21 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 21 134 (Polychromatic418967fa.accept_15_8_6_14_1_975 8 21 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 134 (accept_3_2 7 21 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 134 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 21 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 134
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 21 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 21 134 (accept_3_2 4 21 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21
  134 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 21 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 21 134 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 21 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 134 (accept_3_2 1 21 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 21 134))))))))))))))))))))) (allB_succ 20 134 (allA_succ_of_accept 19 20 134 (accept_3_2 19 20
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 134 2 9 10 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 20 134
  (Polychromatic418967fa.accept_12_5_8_2_1_309 17 20 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 20 134 2 8 10 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 20 134 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 20 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 20 134 2 7 10 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 134 (accept_3_2 13 20 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 20 134 2 6 10 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 20 134 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 20 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 134 2 5 10 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 134 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 20
  134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 20 134 2 4 10 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 20 134 (accept_3_2 7 20
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 134 2 3 10 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 20 134
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 20 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 20 134 2 2 10 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 20 134 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 20 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 134 2 1 10 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 134 (accept_3_2 1 20 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 134)))))))))))))))))))) (allB_succ 19 134 (allA_of_3_0 19 19 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 18 134 (allA_succ_of_accept 17 18 134 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 18 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 134 2 8 9 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 134
  (Polychromatic418967fa.accept_12_3_6_2_1_747 15 18 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 18 134 2 7 9 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 134 (accept_3_2 13 18 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18
  134 2 6 9 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  18 134 (Polychromatic418967fa.accept_14_11_4_8_1_664 11 18 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 134 2 5 9 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 18 134 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 18 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 134 2 4 9 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 134 (accept_3_2 7 18 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 134 2 3 9 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 18 134 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 18 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 134 2 2 9 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 134
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 18 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 134 2 1 9 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 134 (accept_3_2 1 18 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18
  134)))))))))))))))))) (allB_succ 17 134 (allA_succ_of_accept 16 17 134 (accept_3_2 16 17 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 17 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 134
  (Polychromatic418967fa.accept_19_14_17_1_1_2788 14 17 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 134 (accept_3_2 13 17 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 134 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 17 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 17 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 134 (accept_3_2 10 17 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 17 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 134
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 17 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 134 (accept_3_2 7 17 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  134 (Polychromatic418967fa.accept_22_6_17_2_1_3518 6 17 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 17 134 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 17 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 134 (accept_3_2 4 17 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 17 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 17 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 134
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 17 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 17 134 (accept_3_2 1 17 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17
  134))))))))))))))))) (allB_succ 16 134 (allA_of_3_0 16 16 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15
  134 (allA_succ_of_accept 14 15 134 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 15 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 134 (accept_3_2 13 15 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 15 134 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 15 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 11
  15 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 134 (accept_3_2 10 15
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 9
  15 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 134
  (Polychromatic418967fa.accept_19_8_15_1_1_3979 8 15 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 134 (accept_3_2 7 15 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15
  134 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 15 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 15 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 134 (accept_3_2 4 15 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 15 134 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 15 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 134 (Polychromatic418967fa.accept_9_2_6_8_1_321 2
  15 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 134 (accept_3_2 1 15 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 134))))))))))))))) (allB_succ 14 134 (allA_succ_of_accept 13 14
  134 (accept_3_2 13 14 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 134 2 6 7 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 134
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 14 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 14 134 2 5 7 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 14 134 (Polychromatic418967fa.accept_19_9_14_1_1_6792 9 14 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 14 134 2 4 7 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 14 134 (accept_3_2 7 14 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 14 134 2 3 7 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 14 134 (Polychromatic418967fa.accept_13_5_1_4_1_3966 5 14 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 14 134 2 2 7 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 14 134 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 14
  134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 134 2 1 7 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 134 (accept_3_2 1 14
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14 134)))))))))))))) (allB_succ 13 134 (allA_of_3_0 13 13 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 12 134 (allA_succ_of_accept 11 12 134
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 12 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 12 134 2 5 6 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 12 134 (Polychromatic418967fa.accept_15_9_12_14_1_963 9 12 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 12 134 2 4 6 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 12 134 (accept_3_2 7 12 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 12 134 2 3 6 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 12 134 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 12 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 134 2 2 6 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 12 134 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 12
  134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 134 2 1 6 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 134 (accept_3_2 1 12
  134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 134)))))))))))) (allB_succ 11 134 (allA_succ_of_accept 10 11
  134 (accept_3_2 10 11 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 134
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 11 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 134 (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 11 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 134 (accept_3_2 7 11 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 134 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 11 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 134 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 11
  134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 134 (accept_3_2 4 11 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 134 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 11
  134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 134
  (Polychromatic418967fa.accept_13_2_11_4_1_445 2 11 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 134 (accept_3_2 1 11 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  134))))))))))) (allB_succ 10 134 (allA_of_3_0 10 10 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 134
  (allA_succ_of_accept 8 9 134 (Polychromatic418967fa.accept_10_8_9_4_1_961 8 9 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 134 (accept_3_2 7 9 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 9 134 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 9 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 134 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 9
  134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 134 (accept_3_2 4 9 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 9
  134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 134
  (Polychromatic418967fa.accept_16_2_9_6_1_4441 2 9 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 134 (accept_3_2 1 9 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 134)))))))))
  (allB_succ 8 134 (allA_succ_of_accept 7 8 134 (accept_3_2 7 8 134 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 8 134 2 3 4 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 8 134 (Polychromatic418967fa.accept_11_5_8_2_1_588 5 8 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 8 134 2 2 4 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 8 134 (Polychromatic418967fa.accept_20_3_8_14_1_5342 3 8 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 134 2 1 4 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 134 (accept_3_2 1 8 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 8 134)))))))) (allB_succ 7 134 (allA_of_3_0 7 7 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 6 134 (allA_succ_of_accept 5 6 134 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 6 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 134 2 2 3 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 134
  (Polychromatic418967fa.accept_9_3_6_8_1_308 3 6 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 134 2 1 3 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 134 (accept_3_2 1 6 134 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 134))))))
  (allB_succ 5 134 (allA_succ_of_accept 4 5 134 (accept_3_2 4 5 134 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 5 134 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 5 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 134 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 5 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 134 (accept_3_2 1 5 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 5 134))))) (allB_succ 4 134 (allA_of_3_0 4 4 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 3 134 (allA_succ_of_accept 2 3 134 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 3 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 134 (accept_3_2 1 3 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 3 134))) (allB_succ 2 134 (allA_succ_of_accept 1 2 134 (accept_3_2 1 2 134
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 134)) (allB_two
  134))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


